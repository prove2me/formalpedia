-- Prove2me | Theorems.Thm_P2M_GlobalTheory_toH__cechHEquivCohOn_d09ae21bbaab
-- name    : P2M_GlobalTheory_toH__cechHEquivCohOn_d09ae21bbaab
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:34:01.520141+00:00
-- url     : https://prove2.me/theorems/91b45e26-cb6e-46e8-bca9-05838a711b48
-- title:
--   P2 M Global Theory to H  cech HEquiv Coh On d09ae21bbaab: P2 M Global Theory to H  cech HEquiv Coh On d09ae21bbaab
-- statement:
--   The P2 M Global Theory to H  cech HEquiv Coh On d09ae21bbaab construction uses the P2 M Global Theory to H  cech HEquiv Coh On d09ae21bbaab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CechModulesFunctorShortExactOfAcyclic.lean#L381-L384
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CechModulesFunctorShortExactOfAcyclic.lean#L381-L384

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PresheafCubeExactAtSuccOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SumNegOnePowFinrankEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsAddEquivOfSurjectiveOfKerIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CechModulesFunctorShortExactOfAcyclic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite
universe v u
noncomputable section
open GlobalTheory
variable {X : Scheme.{u}} {ι : Type}
variable {V : X.Opens} {U : ι → X.Opens} {F G : X.Modules}
variable [LinearOrder ι] (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)]
variable [Finite ι] (hc : V ≤ ⨆ i, U i)

theorem P2M_GlobalTheory_toH__cechHEquivCohOn_d09ae21bbaab (hF : CechAcyclicMod V U F) (n : ℕ) (x : cechAbH F.presheaf V U n) :
    cohOn.toH' F V n (cechHEquivCohOn R hc hF n (cechAbHEquiv R F V U n x)) =
      cechAbHEquivH' (T := X.toPresheafedSpace.carrier) hc (cechAcyclicMod_iff.1 hF) n x := by sorry

alias «GlobalTheory».«toH'_cechHEquivCohOn» := P2M_GlobalTheory_toH__cechHEquivCohOn_d09ae21bbaab
