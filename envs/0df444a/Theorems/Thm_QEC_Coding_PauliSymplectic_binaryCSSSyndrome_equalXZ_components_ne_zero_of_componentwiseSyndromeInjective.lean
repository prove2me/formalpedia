-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_binaryCSSSyndrome_equalXZ_components_ne_zero_of_componentwiseSyndromeInjective
-- name    : QEC.Coding.PauliSymplectic.binaryCSSSyndrome_equalXZ_components_ne_zero_of_componentwiseSyndromeInjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:43:57.34124+00:00
-- url     : https://prove2.me/theorems/61ab3524-8fe2-452a-8438-d225e62f374c
-- title:
--   Pauli Symplectic: binary CSSSyndrome equal XZ components ne zero of componentwise Syndrome Injective
-- statement:
--   A nonzero equal-X/Z support word inside both injectivity balls has nonzero
--   classical syndromes in both sectors, and its CSS syndrome is their tagged pair.
--   This is the conditional Y-support corollary of [Gott97, Ch. 3, CSS Y-error
--   two-component scope].
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/Correctability.lean#L149-L182
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/Correctability.lean#L149-L182

import Definitions.Def_QEC_Coding_CSS_Syndrome
import Definitions.Def_QEC_Coding_Stabilizer_Correctability
import Definitions.Def_QEC_Coding_CSS_Correctability
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PauliSymplectic
universe u v
variable {iota kappaP kappaQ : Type u} [Fintype iota] [DecidableEq iota]
  [Fintype kappaP] [Fintype kappaQ]
omit [DecidableEq iota]

theorem QEC.Coding.PauliSymplectic.binaryCSSSyndrome_equalXZ_components_ne_zero_of_componentwiseSyndromeInjective
    (P : Word (ZMod 2) iota →ₗ[ZMod 2] Word (ZMod 2) kappaP)
    (Q : Word (ZMod 2) iota →ₗ[ZMod 2] Word (ZMod 2) kappaQ)
    (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
    {tX tZ : Nat}
    (hP : ∀ x y : Word (ZMod 2) iota,
      HammingWeight x ≤ tX → HammingWeight y ≤ tX → P x = P y → x = y)
    (hQ : ∀ z w : Word (ZMod 2) iota,
      HammingWeight z ≤ tZ → HammingWeight w ≤ tZ → Q z = Q w → z = w)
    (phase : ZMod 2) (y : Word (ZMod 2) iota)
    (hy : y ≠ 0) (hyX : HammingWeight y ≤ tX) (hyZ : HammingWeight y ≤ tZ) :
    P y ≠ 0 ∧ Q y ≠ 0 ∧
      stabilizerSyndrome (binaryCSSParityCheckGenerators P Q)
          ({ phase := phase, vector := { xPart := y, zPart := y } } : Binary iota) =
        Sum.elim (P y) (Q y) ∧
      (fun p => stabilizerSyndrome (binaryCSSParityCheckGenerators P Q)
        ({ phase := phase, vector := { xPart := y, zPart := y } } : Binary iota)
        (Sum.inl p)) ≠ 0 ∧
      (fun q => stabilizerSyndrome (binaryCSSParityCheckGenerators P Q)
        ({ phase := phase, vector := { xPart := y, zPart := y } } : Binary iota)
        (Sum.inr q)) ≠ 0 := by sorry
