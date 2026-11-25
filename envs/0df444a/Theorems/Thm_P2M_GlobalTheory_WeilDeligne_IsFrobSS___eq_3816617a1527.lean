-- Prove2me | Theorems.Thm_P2M_GlobalTheory_WeilDeligne_IsFrobSS___eq_3816617a1527
-- name    : P2M_GlobalTheory_WeilDeligne_IsFrobSS___eq_3816617a1527
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T18:17:39.747214+00:00
-- url     : https://prove2.me/theorems/febfe1d8-d12d-5b8a-8142-24c4606c4e26
-- title:
--   P2 M Global Theory Weil Deligne Is Frob SS   eq 3816617a1527: P2 M Global Theory Weil Deligne Is Frob SS   eq 3816617a1527
-- statement:
--   The P2 M Global Theory Weil Deligne Is Frob SS   eq 3816617a1527 construction uses the P2 M Global Theory Weil Deligne Is Frob SS   eq 3816617a1527 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/CharpolyEqOfIsNilpotentSub.lean#L98-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/CharpolyEqOfIsNilpotentSub.lean#L98-L101

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

theorem P2M_GlobalTheory_WeilDeligne_IsFrobSS___eq_3816617a1527 {ρ : Weil h → End ℂ V} {N : End ℂ V} {a : WDRep h V} (ha : IsFrobSS ρ N a)
    {g : Weil h} (hg : (ρ g).IsSemisimple) : a.ρ g = ρ g := by sorry

alias «GlobalTheory».«WeilDeligne».«IsFrobSS».«ρ_eq» := P2M_GlobalTheory_WeilDeligne_IsFrobSS___eq_3816617a1527
