-- Prove2me | Theorems.Thm_P2M_GlobalTheory___cechClass_89909f0dccc0
-- name    : P2M_GlobalTheory___cechClass_89909f0dccc0
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:40:08.711122+00:00
-- url     : https://prove2.me/theorems/8d54fd02-8995-49d8-bd6b-1272aad72ac2
-- title:
--   P2 M Global Theory   cech Class 89909f0dccc0: P2 M Global Theory   cech Class 89909f0dccc0
-- statement:
--   The P2 M Global Theory   cech Class 89909f0dccc0 construction uses the P2 M Global Theory   cech Class 89909f0dccc0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CechModulesFunctorShortExactOfAcyclic.lean#L31-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CechModulesFunctorShortExactOfAcyclic.lean#L31-L59

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
variable {ι : Type} [LinearOrder ι] {R : Type v} [Ring R]

theorem P2M_GlobalTheory___cechClass_89909f0dccc0 {S : ShortComplex (Cube.{u} ι R)}
    (hS : (S.map (cechFunctor ι R)).ShortExact) (p : ℕ)
    (x₃ : LinearMap.ker (Cube.d S.X₃ (p + 1))) (x₂ : Cube.Term S.X₂ (p + 1))
    (x₁ : LinearMap.ker (Cube.d S.X₁ (p + 1 + 1)))
    (h₂ : Cube.termMap S.g (p + 1) x₂ = x₃.1)
    (h₁ : Cube.termMap S.f (p + 1 + 1) x₁.1 = Cube.d S.X₂ (p + 1) x₂) :
    (hS.δ p (p + 1) rfl).hom (cechClass S.X₃ p x₃) = cechClass S.X₁ (p + 1) x₁ := by sorry

alias «GlobalTheory».«δ_cechClass» := P2M_GlobalTheory___cechClass_89909f0dccc0
