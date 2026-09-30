-- Prove2me | Theorems.Thm_UnderstandingML_compression_bound_consistent
-- name    : UnderstandingML.compression_bound_consistent
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T06:01:09.225993+00:00
-- url     : https://prove2.me/theorems/7f309576-eba0-455c-ac6c-00bc4dbea955
-- title:
--   Corollary 30.3: under the conditions of Theorem 30.2, if L_V(A(S)) = 0 then L_D(A(S)) ≤ 8k log(m/δ)/m w.p. ≥ 1 − δ
-- statement:
--   **Corollary 30.3.** Assuming the conditions of Theorem 30.2, and further assuming that $L_V(A(S)) = 0$, then, with probability of at least $1 - \delta$ over the choice of $S$ we have $L_D(A(S)) \le \frac{8k\log(m/\delta)}{m}$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §30.1 p. 411, Corollary 30.3

import Definitions.Def_UnderstandingML_Compression

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Corollary 30.3** (p. 411). Assuming the conditions of Theorem 30.2, and further assuming
that `L_V(A(S)) = 0`, then with probability of at least `1 − δ` over the choice of `S`,
`L_D(A(S)) ≤ 8k log(m/δ)/m`. -/
theorem compression_bound_consistent {Z Hyp : Type*} [MeasurableSpace Z] (loss : Hyp → Z → ℝ)
    (hloss : ∀ h z, loss h z ∈ Set.Icc (0 : ℝ) 1) (D : Measure Z) [IsProbabilityMeasure D]
    (k m : ℕ) (hk : 1 ≤ k) (hm : 2 * k ≤ m) (hm0 : 0 < m) (B : (Fin k → Z) → Hyp)
    (hB : Measurable (fun p : (Fin k → Z) × Z ↦ loss (B p.1) p.2))
    (sel : (Fin m → Z) → Fin k → Fin m) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    iidLaw D m {S | heldOutRisk loss sel S (compressedHyp B sel S) = 0 ∧
        8 * k * Real.log (m / δ) / m < risk loss D (compressedHyp B sel S)} ≤
      ENNReal.ofReal δ := by sorry

end UnderstandingML
