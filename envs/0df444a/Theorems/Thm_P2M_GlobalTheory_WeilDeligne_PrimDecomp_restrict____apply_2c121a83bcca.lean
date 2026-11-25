-- Prove2me | Theorems.Thm_P2M_GlobalTheory_WeilDeligne_PrimDecomp_restrict____apply_2c121a83bcca
-- name    : P2M_GlobalTheory_WeilDeligne_PrimDecomp_restrict____apply_2c121a83bcca
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T17:58:24.529624+00:00
-- url     : https://prove2.me/theorems/6b3012f8-85d4-4b85-99dd-171d5ff16aa4
-- title:
--   P2 M Global Theory Weil Deligne Prim Decomp restrict    apply 2c121a83bcca: P2 M Global Theory Weil Deligne Prim Decomp restrict    apply 2c121a83bcca
-- statement:
--   The P2 M Global Theory Weil Deligne Prim Decomp restrict    apply 2c121a83bcca construction uses the P2 M Global Theory Weil Deligne Prim Decomp restrict    apply 2c121a83bcca property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RestrictHomApply.lean#L68-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RestrictHomApply.lean#L68-L70

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RestrictHomApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module
open GlobalTheory GlobalTheory.WeilDeligne GlobalTheory.WeilDeligne.PrimDecomp
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem P2M_GlobalTheory_WeilDeligne_PrimDecomp_restrict____apply_2c121a83bcca (a : WDRep h V) (S : Submodule ℂ V)
    (hS : ∀ σ, ∀ v ∈ S, a.ρ σ v ∈ S) (σ : Weil h) (v : S) :
    (((restrictρ a S hS).ρ σ v : S) : V) = a.ρ σ v := by sorry

alias «GlobalTheory».«WeilDeligne».«PrimDecomp».«restrictρ_ρ_apply» := P2M_GlobalTheory_WeilDeligne_PrimDecomp_restrict____apply_2c121a83bcca

attribute [defeq] P2M_GlobalTheory_WeilDeligne_PrimDecomp_restrict____apply_2c121a83bcca
