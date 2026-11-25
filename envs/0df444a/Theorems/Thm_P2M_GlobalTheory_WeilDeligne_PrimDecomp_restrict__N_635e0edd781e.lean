-- Prove2me | Theorems.Thm_P2M_GlobalTheory_WeilDeligne_PrimDecomp_restrict__N_635e0edd781e
-- name    : P2M_GlobalTheory_WeilDeligne_PrimDecomp_restrict__N_635e0edd781e
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T17:58:04.500276+00:00
-- url     : https://prove2.me/theorems/9808703f-d8a1-4e46-9bb8-4c8549fa6955
-- title:
--   P2 M Global Theory Weil Deligne Prim Decomp restrict  N 635e0edd781e: P2 M Global Theory Weil Deligne Prim Decomp restrict  N 635e0edd781e
-- statement:
--   The P2 M Global Theory Weil Deligne Prim Decomp restrict  N 635e0edd781e construction uses the P2 M Global Theory Weil Deligne Prim Decomp restrict  N 635e0edd781e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RestrictHomApply.lean#L72-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RestrictHomApply.lean#L72-L73

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

theorem P2M_GlobalTheory_WeilDeligne_PrimDecomp_restrict__N_635e0edd781e (a : WDRep h V) (S : Submodule ℂ V)
    (hS : ∀ σ, ∀ v ∈ S, a.ρ σ v ∈ S) : (restrictρ a S hS).N = 0 := by sorry

alias «GlobalTheory».«WeilDeligne».«PrimDecomp».«restrictρ_N» := P2M_GlobalTheory_WeilDeligne_PrimDecomp_restrict__N_635e0edd781e

attribute [defeq] P2M_GlobalTheory_WeilDeligne_PrimDecomp_restrict__N_635e0edd781e
