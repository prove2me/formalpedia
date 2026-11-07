-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_binaryCSSParityChecks_exists_finiteKrausCorrectable_of_componentwiseSyndromeInjective
-- name    : QEC.Coding.PauliSymplectic.binaryCSSParityChecks_exists_finiteKrausCorrectable_of_componentwiseSyndromeInjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:43:58.386732+00:00
-- url     : https://prove2.me/theorems/d4f61247-949d-4130-bb8b-aba6da70ce1a
-- title:
--   Pauli Symplectic: binary CSSParity Checks exists finite Kraus Correctable of componentwise Syndrome Injective
-- statement:
--   Bounded injectivity of the two classical CSS syndrome maps corrects every
--   complete finite binary-Pauli Kraus family whose active X and Z components obey
--   the corresponding separate bounds. The conclusion is an actual CPTP recovery
--   for the exact common-fixed parity-check CSS code. This realizes the derived
--   semantic bridge from [Gott97, Ch. 3, CSS componentwise X/Z/Y correction scope]
--   through the support-sensitive stabilizer criterion and Knill-Laflamme recovery.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/Correctability.lean#L267-L293
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/Correctability.lean#L267-L293

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

theorem QEC.Coding.PauliSymplectic.binaryCSSParityChecks_exists_finiteKrausCorrectable_of_componentwiseSyndromeInjective
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
      HammingWeight (E a).vector.zPart ≤ tZ)
    (hcomplete : (binaryPauliKrausFamily E amp).Complete) :
    ∃ recovery : Semantics.QuantumChannel
        (Semantics.Qubit.QubitRegister iota) (Semantics.Qubit.QubitRegister iota),
      Semantics.FiniteKrausCorrectable alpha
        (Semantics.Qubit.QubitRegister iota) (Semantics.Qubit.QubitRegister iota)
        (binaryCSSStabilizerCodeOfParityChecks P Q horth).code
        (binaryPauliKrausFamily E amp) recovery := by sorry
