-- Prove2me | Theorems.Thm_P2M_GlobalTheory_cechHEquivCohOn___93c7f0989749
-- name    : P2M_GlobalTheory_cechHEquivCohOn___93c7f0989749
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:37:45.302587+00:00
-- url     : https://prove2.me/theorems/88afbd58-6415-54f8-a7af-6c3b24307027
-- title:
--   P2 M Global Theory cech HEquiv Coh On   93c7f0989749: P2 M Global Theory cech HEquiv Coh On   93c7f0989749
-- statement:
--   The P2 M Global Theory cech HEquiv Coh On   93c7f0989749 construction uses the P2 M Global Theory cech HEquiv Coh On   93c7f0989749 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CechModulesFunctorShortExactOfAcyclic.lean#L392-L402
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CechModulesFunctorShortExactOfAcyclic.lean#L392-L402

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

theorem P2M_GlobalTheory_cechHEquivCohOn___93c7f0989749 {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h₁ : CechAcyclicMod V U S.X₁) (h₃ : CechAcyclicMod V U S.X₃) (n : ℕ)
    (x : cechH R S.X₃ V U n) :
    cechHEquivCohOn R hc h₁ (n + 1) (cechδ R hS h₁ n x) =
      cohOn.δ R hS V n (cechHEquivCohOn R hc h₃ n x) := by sorry

alias «GlobalTheory».«cechHEquivCohOn_δ» := P2M_GlobalTheory_cechHEquivCohOn___93c7f0989749
