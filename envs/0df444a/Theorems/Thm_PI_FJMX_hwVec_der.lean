-- Prove2me | Theorems.Thm_PI_FJMX_hwVec_der
-- name    : PI.FJMX.hwVec_der
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:06:19.15935+00:00
-- url     : https://prove2.me/theorems/5518d426-ee82-41e0-b5e9-be6488af5bca
-- title:
--   FJMX: hw Vec der
-- statement:
--   The FJMX construction uses the hw Vec der property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ExistHW.lean#L235-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ExistHW.lean#L235-L247

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistHW
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial FockH1Action PI.FJM
noncomputable section
open PI PI.FJMX
variable {p q r s : ℕ}

theorem PI.FJMX.hwVec_der (D : Derivation ℂ (Pol p q r s) (Pol p q r s)) (a b c d : List ℤ)
    (h1 : ∀ t, D (leadT (varMat (fun i : Fin p => (Sum.inl i : Ix p q))
      (fun k : Fin r => (Sum.inl k : Ix r s))) t) = 0)
    (h2 : ∀ t, D (leadT (varMat (fun i : Fin p => (Sum.inl (Fin.rev i) : Ix p q))
      (fun l : Fin s => (Sum.inr (Fin.rev l) : Ix r s))) t) = 0)
    (h3 : ∀ t, D (leadT (varMat (fun j : Fin q => (Sum.inr j : Ix p q))
      (fun l : Fin s => (Sum.inr l : Ix r s))) t) = 0)
    (h4 : ∀ t, D (leadT (varMat (fun j : Fin q => (Sum.inr (Fin.rev j) : Ix p q))
      (fun k : Fin r => (Sum.inl (Fin.rev k) : Ix r s))) t) = 0) :
    D (hwVec p q r s a b c d) = 0 := by sorry
