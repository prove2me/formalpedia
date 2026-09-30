-- Prove2me | Theorems.Thm_UnderstandingML_eps_net_theorem
-- name    : UnderstandingML.eps_net_theorem
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T05:55:57.866131+00:00
-- url     : https://prove2.me/theorems/dfb2b96a-0afb-4e0c-a174-e965735dfc49
-- title:
--   Theorem 28.3: for VCdim(H) = d, ε ∈ (0,1), δ ∈ (0,1/4) and m ≥ (8/ε)(2d log(16e/ε) + log(2/δ)), S ∼ D^m is an ε-net for H with probability ≥ 1 − δ
-- statement:
--   **Theorem 28.3.** Let $H \subset 2^X$ with $\operatorname{VCdim}(H) = d$. Fix $\epsilon \in (0,1)$, $\delta \in (0, 1/4)$ and let
--   $$m \ge \frac{8}{\epsilon}\Big(2d\log\Big(\frac{16e}{\epsilon}\Big) + \log\Big(\frac2\delta\Big)\Big).$$
--   Then, with probability of at least $1 - \delta$ over a choice of $S \sim D^m$ we have that $S$ is an $\epsilon$-net for $H$. $H$ consists of measurable hypotheses with the countable-approximation property of Mission IV (Remark 3.1).
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §28.3 pp. 398-400, Theorem 28.3 with its proof

import Definitions.Def_UnderstandingML_FundamentalProof

open MeasureTheory

namespace UnderstandingML

/-- **Theorem 28.3** (p. 398). Let `H ⊆ 2^X` with `VCdim(H) = d`. Fix `ε ∈ (0, 1)`, `δ ∈ (0, 1/4)`
and let `m ≥ (8/ε)(2d log(16e/ε) + log(2/δ))`. Then, with probability of at least `1 − δ` over a
choice of `S ∼ D^m` we have that `S` is an `ε`-net for `H`. Measurable `H` with the
countable-approximation property (Remark 3.1). -/
theorem eps_net_theorem {X : Type*} [MeasurableSpace X] (H : Set (X → Bool))
    (hH : ∀ h ∈ H, Measurable h) (hsep : PointwiseSeparable H) (d : ℕ) (hd : vcDim H = d)
    (D : Measure X) [IsProbabilityMeasure D] (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ)
    (hδ1 : δ < 1 / 4) (m : ℕ)
    (hm : 8 / ε * (2 * d * Real.log (16 * Real.exp 1 / ε) + Real.log (2 / δ)) ≤ m) :
    iidLaw D m {S | ¬ IsEpsNet H D ε S} ≤ ENNReal.ofReal δ := by sorry

end UnderstandingML
