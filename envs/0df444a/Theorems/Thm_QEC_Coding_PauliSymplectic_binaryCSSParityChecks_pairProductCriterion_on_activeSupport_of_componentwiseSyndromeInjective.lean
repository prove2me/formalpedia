-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_binaryCSSParityChecks_pairProductCriterion_on_activeSupport_of_componentwiseSyndromeInjective
-- name    : QEC.Coding.PauliSymplectic.binaryCSSParityChecks_pairProductCriterion_on_activeSupport_of_componentwiseSyndromeInjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:20:58.294823+00:00
-- url     : https://prove2.me/theorems/473c1234-2ba8-4561-b4ad-15b5fb3c116e
-- title:
--   Pauli Symplectic: binary CSSParity Checks pair Product Criterion on active Support of componentwise Syndrome Injective
-- statement:
--   Separate bounded injectivity of the P-row/Z-check and Q-row/X-check classical
--   syndrome maps gives the active-support stabilizer pair-product dichotomy for
--   the exact source-valid parity-check CSS stabilizer.
--
--   This is an internal API lemma: it neither assumes nor concludes
--   Knill-Laflamme, completeness, recovery, or correctability.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/Correctability.lean#L112-L140
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/Correctability.lean#L112-L140

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

theorem QEC.Coding.PauliSymplectic.binaryCSSParityChecks_pairProductCriterion_on_activeSupport_of_componentwiseSyndromeInjective
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
    ∀ a b, amp a ≠ 0 → amp b ≠ 0 →
      (binaryCSSSourceValidStabilizerOfParityChecks P Q horth).1.InGeneratedGroupUpToSign
          (binaryMul (binaryDagger (E a)) (E b)) ∨
        ¬ (binaryCSSSourceValidStabilizerOfParityChecks P Q horth).1.InBinaryNormalizer
          (binaryMul (binaryDagger (E a)) (E b)) := by sorry
