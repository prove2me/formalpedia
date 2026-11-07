-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_binaryCSSParityChecks_sameSpaceKnillLaflammeCriterion_of_componentwiseSyndromeInjective
-- name    : QEC.Coding.PauliSymplectic.binaryCSSParityChecks_sameSpaceKnillLaflammeCriterion_of_componentwiseSyndromeInjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:27:50.121761+00:00
-- url     : https://prove2.me/theorems/120d1413-c45a-4670-8d59-d55ba1c644bb
-- title:
--   Pauli Symplectic: binary CSSParity Checks same Space Knill Laflamme Criterion of componentwise Syndrome Injective
-- statement:
--   Bounded injectivity of the two classical CSS syndrome maps gives the
--   same-space Knill-Laflamme criterion for every finite binary-Pauli family whose
--   active X and Z components obey the corresponding separate bounds.
--
--   The conclusion is the exact matrix-element criterion on the actual common
--   +1 fixed parity-check CSS carrier; it requires neither completeness nor a
--   recovery channel.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/Correctability.lean#L193-L214
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/Correctability.lean#L193-L214

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

theorem QEC.Coding.PauliSymplectic.binaryCSSParityChecks_sameSpaceKnillLaflammeCriterion_of_componentwiseSyndromeInjective
    {alpha : Type v} [Fintype alpha]
    (P : Word (ZMod 2) iota →ₗ[ZMod 2] Word (ZMod 2) kappaP)
    (Q : Word (ZMod 2) iota →ₗ[ZMod 2] Word (ZMod 2) kappaQ)
    (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
    (tX tZ : Nat)
    (hP : ∀ x y : Word (ZMod 2) iota,
      HammingWeight x ≤ tX → HammingWeight y ≤ tX → P x = P y → x = y)
    (hQ : ∀ z w : Word (ZMod 2) iota,
      HammingWeight z ≤ tZ → HammingWeight w ≤ tZ → Q z = Q w → z = w)
    (E : alpha → Binary iota) (amp : alpha → Complex)
    (hbound : ∀ a, amp a ≠ 0 →
      HammingWeight (E a).vector.xPart ≤ tX ∧
      HammingWeight (E a).vector.zPart ≤ tZ) :
    (binaryPauliKrausFamily E amp).sameSpaceKnillLaflammeCriterion
      (binaryCSSStabilizerCodeOfParityChecks P Q horth).code := by sorry
