-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_binaryCSSParityChecks_exists_finiteKrausCorrectable_and_correctable_toQuantumChannel_of_componentwiseSyndromeInjective
-- name    : QEC.Coding.PauliSymplectic.binaryCSSParityChecks_exists_finiteKrausCorrectable_and_correctable_toQuantumChannel_of_componentwiseSyndromeInjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:44:04.817615+00:00
-- url     : https://prove2.me/theorems/0fac3cd0-5242-482b-88e1-ab8f8e67f755
-- title:
--   Pauli Symplectic: binary CSSParity Checks exists finite Kraus Correctable and correctable to Quantum Channel of componentwise Syndrome Injective
-- statement:
--   Bounded injectivity of the two classical CSS syndrome maps corrects every
--   complete finite binary-Pauli Kraus family whose active X and Z components obey
--   the corresponding separate bounds. One M2 recovery witnesses both raw
--   finite-Kraus correctability and bundled-channel semantic correctability for the
--   same common-fixed parity-check CSS code and the same family.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/Correctability.lean#L223-L257
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/Correctability.lean#L223-L257

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

theorem QEC.Coding.PauliSymplectic.binaryCSSParityChecks_exists_finiteKrausCorrectable_and_correctable_toQuantumChannel_of_componentwiseSyndromeInjective
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
        (binaryPauliKrausFamily E amp) recovery ∧
      Semantics.Correctable
        (Semantics.Qubit.QubitRegister iota) (Semantics.Qubit.QubitRegister iota)
        (binaryCSSStabilizerCodeOfParityChecks P Q horth).code
        ((binaryPauliKrausFamily E amp).toQuantumChannel hcomplete) recovery := by sorry
