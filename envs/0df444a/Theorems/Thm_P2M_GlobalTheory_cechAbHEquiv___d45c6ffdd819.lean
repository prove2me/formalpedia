-- Prove2me | Theorems.Thm_P2M_GlobalTheory_cechAbHEquiv___d45c6ffdd819
-- name    : P2M_GlobalTheory_cechAbHEquiv___d45c6ffdd819
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:39:23.560805+00:00
-- url     : https://prove2.me/theorems/5554ec39-530c-4986-9899-c5ba2dc7d774
-- title:
--   P2 M Global Theory cech Ab HEquiv   d45c6ffdd819: P2 M Global Theory cech Ab HEquiv   d45c6ffdd819
-- statement:
--   The P2 M Global Theory cech Ab HEquiv   d45c6ffdd819 construction uses the P2 M Global Theory cech Ab HEquiv   d45c6ffdd819 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CechModulesFunctorShortExactOfAcyclic.lean#L336-L347
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CechModulesFunctorShortExactOfAcyclic.lean#L336-L347

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
variable {S S' : ShortComplex X.Modules} (hS : S.ShortExact) (h₁ : CechAcyclicMod V U S.X₁)

theorem P2M_GlobalTheory_cechAbHEquiv___d45c6ffdd819 (n : ℕ) (x : cechAbH S.X₃.presheaf V U n) :
    cechAbHEquiv R S.X₁ V U (n + 1) (cechAbδ (T := X.toPresheafedSpace.carrier)
        (shortExact_toAbSheaf hS) (cechAcyclicMod_iff.1 h₁) n x) =
      cechδ R hS h₁ n (cechAbHEquiv R S.X₃ V U n x) := by sorry

alias «GlobalTheory».«cechAbHEquiv_δ» := P2M_GlobalTheory_cechAbHEquiv___d45c6ffdd819
