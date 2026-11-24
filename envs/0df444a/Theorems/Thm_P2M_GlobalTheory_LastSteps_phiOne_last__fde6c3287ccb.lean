-- Prove2me | Theorems.Thm_P2M_GlobalTheory_LastSteps_phiOne_last__fde6c3287ccb
-- name    : P2M_GlobalTheory_LastSteps_phiOne_last__fde6c3287ccb
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:41:14.894705+00:00
-- url     : https://prove2.me/theorems/21e6f4f7-b09e-46a0-8a69-96de1ec21edf
-- title:
--   P2 M Global Theory Last Steps phi One last  fde6c3287ccb: P2 M Global Theory Last Steps phi One last  fde6c3287ccb
-- statement:
--   The P2 M Global Theory Last Steps phi One last  fde6c3287ccb construction uses the P2 M Global Theory Last Steps phi One last  fde6c3287ccb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsClopenIsCompactQLat.lean#L450-L452
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsClopenIsCompactQLat.lean#L450-L452

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_DualLiftInvariance
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactQLat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix IsLocalRing
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData
noncomputable section
open GlobalTheory GlobalTheory.LastSteps
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' n'' : Type}
variable [Fintype n] [Fintype n'] (q : Unif k) (LY : Submodule 𝒪[k] (n → k)) [LY.IsLattice k]
  (L'' : Submodule 𝒪[k] (n'' → k)) [L''.IsLattice k] {M A : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup A]
  [Module ℂ A] (x' : Matrix n'' n k) (η : n → k)
omit [Fintype n']

theorem P2M_GlobalTheory_LastSteps_phiOne_last__fde6c3287ccb (fW : {f : Module.Dual 𝓀[k] (Red LY) // f ≠ 0}) :
    phiOne (ofDual LY fW) (lastPair q L'') (withRow x' η) = latInd LY L'' x' * cosetInd q LY fW.1 η := by sorry

alias «GlobalTheory».«LastSteps».«phiOne_last'» := P2M_GlobalTheory_LastSteps_phiOne_last__fde6c3287ccb
