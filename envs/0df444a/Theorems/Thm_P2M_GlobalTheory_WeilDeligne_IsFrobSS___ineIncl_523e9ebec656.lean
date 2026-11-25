-- Prove2me | Theorems.Thm_P2M_GlobalTheory_WeilDeligne_IsFrobSS___ineIncl_523e9ebec656
-- name    : P2M_GlobalTheory_WeilDeligne_IsFrobSS___ineIncl_523e9ebec656
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T18:17:43.87857+00:00
-- url     : https://prove2.me/theorems/b94685a9-238a-5cb9-b8aa-0fda8494c5dd
-- title:
--   P2 M Global Theory Weil Deligne Is Frob SS   ine Incl 523e9ebec656: P2 M Global Theory Weil Deligne Is Frob SS   ine Incl 523e9ebec656
-- statement:
--   The P2 M Global Theory Weil Deligne Is Frob SS   ine Incl 523e9ebec656 construction uses the P2 M Global Theory Weil Deligne Is Frob SS   ine Incl 523e9ebec656 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/CharpolyEqOfIsNilpotentSub.lean#L149-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/CharpolyEqOfIsNilpotentSub.lean#L149-L161

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ToZModPowKummerEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsFrobeniusSemisimplification
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsNilpotentZpowSubOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsAevalEqSmulOnEigenspace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_CharpolyEqOfIsNilpotentSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module
open GlobalTheory GlobalTheory.WeilDeligne
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']

theorem P2M_GlobalTheory_WeilDeligne_IsFrobSS___ineIncl_523e9ebec656 {ρ : Representation ℂ (Weil h) V} {N : End ℂ V} {a : WDRep h V}
    (ha : IsFrobSS ρ N a) (hρ : IsSmooth ρ) (σ : Ine (F := E) A) :
    a.ρ (ineIncl h σ) = ρ (ineIncl h σ) := by sorry

alias «GlobalTheory».«WeilDeligne».«IsFrobSS».«ρ_ineIncl» := P2M_GlobalTheory_WeilDeligne_IsFrobSS___ineIncl_523e9ebec656
