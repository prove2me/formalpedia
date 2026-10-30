-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P30_threeCopyStabilizerTesting
-- name    : QAlgorithms.Papers.Independent.Extend50.P30.threeCopyStabilizerTesting
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:33:28.645856+00:00
-- url     : https://prove2.me/theorems/f40c7733-733e-494d-a2df-a1d033accb3b
-- title:
--   Stabilizer testing from three copies
-- statement:
--   For any $d\geq2$ with $d\equiv1$ or $5\pmod6$ and any $n$, $\Pi_{\rm accept}=(I+V)/2$ is a valid effect on three copies. It accepts every pure stabilizer with certainty. For every normalized input whose stabilizer fidelities are all at most $1-\varepsilon^2$, it obeys the following soundness bound, without a primality hypothesis.
--
--   $$
--   p_{\rm accept}\leq1-\frac{\varepsilon^2}{16d^2}.
--   $$
--
--   This gives the source's stabilizer testing from three copies in the fixed computational-basis and phase conventions.
--
--   **Formalization Note** Pure states carry norm one; stabilizer averages use density matrices to discard global phases. All finite tensor indices are explicitly ordered by copy, then physical qudit.
-- source:
--   Schur-Weyl Duality for the Clifford Group with Applications: Property Testing, a Robust Hudson Theorem, and de Finetti Representations, arXiv:1712.08628v3, PDF p. 62, theorem-8.6

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P30

noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Extend50.P30

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Gap20.P06 (ketBra)

attribute [local instance] Classical.propDecidable

/-- PDF p.62, Theorem 8.6: exact denominator 16*d^2, including composite dimensions in this regime. -/
theorem threeCopyStabilizerTesting (d n : ℕ) [NeZero d] (hd : 2 ≤ d)
    (hmod : d % 6 = 1 ∨ d % 6 = 5) :
    QAlgorithms.IsEffect (threeCopyTest d n) ∧
    ∀ v : EuclideanSpace ℂ (ResidueRegister d n), ‖v‖ = 1 →
      (IsStabilizer v → QAlgorithms.effectProb (threeCopyTest d n)
        (tensorPower 3 (QAlgorithms.pureDensity v)) = 1) ∧
      (∀ epsilon : ℝ, FarFromStabilizers v epsilon →
        QAlgorithms.effectProb (threeCopyTest d n) (tensorPower 3 (QAlgorithms.pureDensity v)) ≤
          1 - epsilon ^ 2 / (16 * (d : ℝ) ^ 2)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P30

end
