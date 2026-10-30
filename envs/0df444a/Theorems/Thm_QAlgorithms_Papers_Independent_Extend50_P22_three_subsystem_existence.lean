-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P22_three_subsystem_existence
-- name    : QAlgorithms.Papers.Independent.Extend50.P22.three_subsystem_existence
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:15:33.100655+00:00
-- url     : https://prove2.me/theorems/c41a84ae-52e6-447d-b8c4-022ac75decf3
-- title:
--   Theorem 5, Eq.(54): existence of accurate three-subsystem covariant codes
-- statement:
--   Fix an integer $d\ge4$. There is a real constant $C_2$, depending only on $d$, such that for every requested tolerance $\varepsilon>0$ there is an isometric code into exactly three finite subsystems carrying irreducible continuous $U(d)$ representations, intertwining the defining logical representation, whose achieved optimal average-entanglement error $e=\sqrt{1-f_e^2}$ under uniform located single erasure satisfies $$0<e\le\varepsilon,\qquad \max_i\ln d_i\le d(d-1)\ln(1/e)+C_2.$$ Fidelity here is root fidelity at the maximally entangled input, optimized over all CPTP recoveries. The size bound uses the achieved error, not the requested tolerance.
-- source:
--   Continuous symmetries and approximate quantum error correction, arXiv:1902.07714v1, PDF p. 16, Theorem 5, Eq.(54): existence of accurate three-subsystem covariant codes

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P22

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P22

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22 (bell)

open QAlgorithms.Papers.Independent.Support21.P09 (Irreducible)

open QAlgorithms.Papers.Independent.Renew46.P45 (symmetricWeight)

/-- PDF p.16, Theorem 5, (54). C2 depends only on d and the logarithm uses achieved error. -/
theorem three_subsystem_existence (d : ℕ) (hd : 4 ≤ d) :
    ∃ C2 : ℝ, ∀ tolerance : ℝ, 0 < tolerance →
      ∃ c : CovariantErasureCodeData d 3, ∃ R : FullAction c,
        (∀ i, QAlgorithms.Papers.Independent.Support21.P09.Irreducible (fun U => (R.localRep i U : Matrix (Fin (c.dims i)) (Fin (c.dims i)) ℂ))) ∧
        0 < errorE c.uniformNoise ∧ errorE c.uniformNoise ≤ tolerance ∧
        c.logDim ≤ (d : ℝ) * (d - 1 : ℝ) * Real.log ((errorE c.uniformNoise)⁻¹) + C2 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P22

end
