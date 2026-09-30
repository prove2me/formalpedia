-- Prove2me | Theorems.Thm_UnderstandingML_erm_finite_class_bound
-- name    : UnderstandingML.erm_finite_class_bound
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T03:26:43.20469+00:00
-- url     : https://prove2.me/theorems/2859b5e2-693b-4dff-8153-f3e9d028c4f4
-- title:
--   Corollary 2.3: for a finite class under realizability, with m ≥ log(|H|/δ)/ε every ERM hypothesis has true error ≤ ε with probability ≥ 1 − δ
-- statement:
--   **Corollary 2.3.** Let $H$ be a finite hypothesis class. Let $\delta \in (0, 1)$ and $\epsilon > 0$ and let $m$ be an integer that satisfies $m \ge \log(|H|/\delta)/\epsilon$. Then, for any labeling function $f$, and for any distribution $D$, for which the realizability assumption holds (that is, for some $h \in H$, $L_{(D,f)}(h) = 0$), with probability of at least $1 - \delta$ over the choice of an i.i.d. sample $S$ of size $m$, we have that for every ERM hypothesis $h_S$, it holds that $L_{(D,f)}(h_S) \le \epsilon$.
--
--   Formally: for a finite class of measurable hypotheses, a distribution $D$ over $X$, a measurable labeling function $f$ with the realizability assumption, $\epsilon > 0$, $\delta \in (0,1)$ and $m \ge \log(|H|/\delta)/\epsilon$, the probability under $D^m$ (of the labeled sample) that some ERM hypothesis for $S$ has true error greater than $\epsilon$ is at most $\delta$ (the proof's bound $|H_B| e^{-\epsilon m} \le |H| e^{-\epsilon m}$).
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §2.3.1 pp. 37-40, Corollary 2.3 with its proof (bad hypotheses, misleading samples, the union bound and (1 − ε)^m ≤ e^{−εm})

import Definitions.Def_UnderstandingML_Framework

open MeasureTheory

namespace UnderstandingML

/-- **Corollary 2.3** (p. 40). Let `H` be a finite hypothesis class, `δ ∈ (0, 1)`, `ε > 0`, and let
`m` be an integer with `m ≥ log(|H|/δ)/ε`. Then, for any labeling function `f` and any
distribution `D` for which the realizability assumption holds, with probability at least
`1 − δ` over the choice of an i.i.d. sample `S` of size `m`, every ERM hypothesis `h_S` satisfies
`L_{(D,f)}(h_S) ≤ ε`. Stated as: the probability that some ERM hypothesis has true error
greater than `ε` is at most `δ` (the proof's bound `|H_B| e^{−εm}`). -/
theorem erm_finite_class_bound {X : Type*} [MeasurableSpace X] (H : Finset (X → Bool))
    (hH : ∀ h ∈ H, Measurable h) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1) (m : ℕ)
    (hm : Real.log (H.card / δ) / ε ≤ m) (D : Measure X) [IsProbabilityMeasure D] (f : X → Bool)
    (hf : Measurable f) (hreal : Realizable (↑H) D f) :
    iidLaw (labeledLaw D f) m {S | ∃ h, IsERM loss01 (↑H) S h ∧ ε < trueError D f h} ≤
      ENNReal.ofReal δ := by sorry

end UnderstandingML
