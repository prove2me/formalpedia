-- Prove2me | Theorems.Thm_P2M_GlobalTheory_WeilDeligne_IsFrobSS___unique_f10a1346b496
-- name    : P2M_GlobalTheory_WeilDeligne_IsFrobSS___unique_f10a1346b496
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T18:18:58.280041+00:00
-- url     : https://prove2.me/theorems/c8f0b00d-6c73-4f0f-a6c4-5b5493ea4974
-- title:
--   P2 M Global Theory Weil Deligne Is Frob SS   unique f10a1346b496: P2 M Global Theory Weil Deligne Is Frob SS   unique f10a1346b496
-- statement:
--   The P2 M Global Theory Weil Deligne Is Frob SS   unique f10a1346b496 construction uses the P2 M Global Theory Weil Deligne Is Frob SS   unique f10a1346b496 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/CharpolyEqOfIsNilpotentSub.lean#L103-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/CharpolyEqOfIsNilpotentSub.lean#L103-L108

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

theorem P2M_GlobalTheory_WeilDeligne_IsFrobSS___unique_f10a1346b496 {ρ : Weil h → End ℂ V} {N N' : End ℂ V} {a b : WDRep h V}
    (ha : IsFrobSS ρ N a) (hb : IsFrobSS ρ N' b) : a.ρ = b.ρ := by sorry

alias «GlobalTheory».«WeilDeligne».«IsFrobSS».«ρ_unique» := P2M_GlobalTheory_WeilDeligne_IsFrobSS___unique_f10a1346b496
