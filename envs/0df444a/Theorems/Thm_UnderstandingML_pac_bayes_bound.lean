-- Prove2me | Theorems.Thm_UnderstandingML_pac_bayes_bound
-- name    : UnderstandingML.pac_bayes_bound
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T06:05:43.887552+00:00
-- url     : https://prove2.me/theorems/6ad1d02f-d3ac-49b3-be1f-d916e81cb155
-- title:
--   Theorem 31.1 (PAC-Bayes): w.p. ≥ 1−δ over S ∼ D^m, every posterior Q with finite divergence has L_D(Q) ≤ L_S(Q) + √((D(Q‖P) + ln(m/δ))/(2(m−1)))
-- statement:
--   **Theorem 31.1.** Let $D$ be an arbitrary distribution over an example domain $Z$. Let $H$ be a hypothesis class and let $\ell : H \times Z \to [0,1]$ be a loss function. Let $P$ be a prior distribution over $H$ and let $\delta \in (0,1)$. Then, with probability of at least $1 - \delta$ over the choice of an i.i.d. training set $S = \{z_1, \dots, z_m\}$ sampled according to $D$, for all distributions $Q$ over $H$ (even such that depend on $S$), we have
--   $$L_D(Q) \le L_S(Q) + \sqrt{\frac{D(Q\|P) + \ln(m/\delta)}{2(m-1)}},$$
--   where $D(Q\|P) = \mathbb{E}_{h \sim Q}[\ln(Q(h)/P(h))]$ is the Kullback–Leibler divergence.
--
--   Formally: $H$ a measurable space, $\ell$ jointly measurable, $m \ge 2$, and $Q$ ranging over the probability measures $Q \ll P$ with $Q$-integrable log-density (the posteriors with a finite divergence; for the others the bound is vacuous).
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §31.1 p. 416, Theorem 31.1 with its proof (pp. 416-417)

import Definitions.Def_UnderstandingML_PACBayes

open MeasureTheory

namespace UnderstandingML

/-- **Theorem 31.1** (p. 416). Let `D` be an arbitrary distribution over an example domain `Z`.
Let `H` be a hypothesis class and let `ℓ : H × Z → [0, 1]` be a loss function. Let `P` be a prior
distribution over `H` and let `δ ∈ (0, 1)`. Then, with probability of at least `1 − δ` over the
choice of an i.i.d. training set `S = {z₁, …, z_m}` sampled according to `D`, for all
distributions `Q` over `H` (even such that depend on `S`), we have
`L_D(Q) ≤ L_S(Q) + √((D(Q‖P) + ln(m/δ)) / (2(m − 1)))`.
The loss is jointly measurable, `m ≥ 2`, and `Q` ranges over the probability measures `Q ≪ P`
with `Q`-integrable log-density (those with a finite divergence). -/
theorem pac_bayes_bound {Z Hyp : Type*} [MeasurableSpace Z] [MeasurableSpace Hyp]
    (loss : Hyp → Z → ℝ) (hmeas : Measurable (Function.uncurry loss))
    (hloss : ∀ h z, loss h z ∈ Set.Icc (0 : ℝ) 1) (D : Measure Z) [IsProbabilityMeasure D]
    (P : Measure Hyp) [IsProbabilityMeasure P] (m : ℕ) (hm : 2 ≤ m) (δ : ℝ) (hδ : 0 < δ)
    (hδ1 : δ < 1) :
    iidLaw D m {S | ∃ Q : Measure Hyp, IsProbabilityMeasure Q ∧ Q ≪ P ∧
      Integrable (fun h ↦ Real.log (Q.rnDeriv P h).toReal) Q ∧
      gibbsEmpRisk loss S Q + Real.sqrt ((klDiv Q P + Real.log (m / δ)) / (2 * (m - 1))) <
        gibbsRisk loss D Q} ≤ ENNReal.ofReal δ := by sorry

end UnderstandingML
