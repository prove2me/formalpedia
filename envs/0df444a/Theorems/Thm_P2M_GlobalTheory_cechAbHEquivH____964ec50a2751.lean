-- Prove2me | Theorems.Thm_P2M_GlobalTheory_cechAbHEquivH____964ec50a2751
-- name    : P2M_GlobalTheory_cechAbHEquivH____964ec50a2751
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:41:10.294276+00:00
-- url     : https://prove2.me/theorems/f25ca440-1727-4156-8dfc-4986aff39bbb
-- title:
--   P2 M Global Theory cech Ab HEquiv H    964ec50a2751: P2 M Global Theory cech Ab HEquiv H    964ec50a2751
-- statement:
--   The P2 M Global Theory cech Ab HEquiv H    964ec50a2751 construction uses the P2 M Global Theory cech Ab HEquiv H    964ec50a2751 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CechModulesFunctorShortExactOfAcyclic.lean#L279-L284
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CechModulesFunctorShortExactOfAcyclic.lean#L279-L284

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
variable {T : TopCat.{u}} {ι : Type}
variable {V : Opens T} {U : ι → Opens T}
variable [LinearOrder ι]
variable [Finite ι] (hc : V ≤ ⨆ i, U i)
variable {F G : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}}

theorem P2M_GlobalTheory_cechAbHEquivH____964ec50a2751
    {S : ShortComplex (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u})} (hS : S.ShortExact)
    (h₁ : CechAcyclic V U S.X₁) (h₃ : CechAcyclic V U S.X₃) (n : ℕ) (x : cechAbH S.X₃.obj V U n) :
    cechAbHEquivH' hc h₁ (n + 1) (cechAbδ hS h₁ n x) =
      SheafLES.δ hS n V (cechAbHEquivH' hc h₃ n x) := by sorry

alias «GlobalTheory».«cechAbHEquivH'_δ» := P2M_GlobalTheory_cechAbHEquivH____964ec50a2751
