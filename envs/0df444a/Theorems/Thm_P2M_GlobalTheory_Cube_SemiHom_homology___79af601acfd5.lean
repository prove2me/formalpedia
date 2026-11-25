-- Prove2me | Theorems.Thm_P2M_GlobalTheory_Cube_SemiHom_homology___79af601acfd5
-- name    : P2M_GlobalTheory_Cube_SemiHom_homology___79af601acfd5
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:40:47.997885+00:00
-- url     : https://prove2.me/theorems/7910aa7f-77a8-460e-99ee-548ba122b00b
-- title:
--   P2 M Global Theory Cube Semi Hom homology   79af601acfd5: P2 M Global Theory Cube Semi Hom homology   79af601acfd5
-- statement:
--   The P2 M Global Theory Cube Semi Hom homology   79af601acfd5 construction uses the P2 M Global Theory Cube Semi Hom homology   79af601acfd5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CechModulesFunctorShortExactOfAcyclic.lean#L79-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CechModulesFunctorShortExactOfAcyclic.lean#L79-L96

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

theorem P2M_GlobalTheory_Cube_SemiHom_homology___79af601acfd5 {R' : Type*} [Ring R'] {σ : R →+* R'}
    {S : ShortComplex (Cube.{u} ι R)} {S' : ShortComplex (Cube.{u} ι R')}
    (hS : (S.map (cechFunctor ι R)).ShortExact) (hS' : (S'.map (cechFunctor ι R')).ShortExact)
    (ψ₁ : Cube.SemiHom σ S.X₁ S'.X₁) (ψ₂ : Cube.SemiHom σ S.X₂ S'.X₂)
    (ψ₃ : Cube.SemiHom σ S.X₃ S'.X₃)
    (hf : ∀ s x, ψ₂.app s ((S.f.app s).hom x) = (S'.f.app s).hom (ψ₁.app s x))
    (hg : ∀ s x, ψ₃.app s ((S.g.app s).hom x) = (S'.g.app s).hom (ψ₂.app s x))
    (p : ℕ) (x : (cechComplex S.X₃).homology p) :
    ψ₁.homology (p + 1) ((hS.δ p (p + 1) rfl).hom x) =
      (hS'.δ p (p + 1) rfl).hom (ψ₃.homology p x) := by sorry

alias «GlobalTheory».«Cube».«SemiHom».«homology_δ» := P2M_GlobalTheory_Cube_SemiHom_homology___79af601acfd5
