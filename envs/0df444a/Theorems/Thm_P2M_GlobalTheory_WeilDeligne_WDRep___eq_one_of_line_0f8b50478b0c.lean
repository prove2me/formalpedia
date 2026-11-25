-- Prove2me | Theorems.Thm_P2M_GlobalTheory_WeilDeligne_WDRep___eq_one_of_line_0f8b50478b0c
-- name    : P2M_GlobalTheory_WeilDeligne_WDRep___eq_one_of_line_0f8b50478b0c
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T17:04:42.680987+00:00
-- url     : https://prove2.me/theorems/d06c4b99-e9b3-5397-a69e-d4cd38ad79a8
-- title:
--   P2 M Global Theory Weil Deligne WDRep   eq one of line 0f8b50478b0c: P2 M Global Theory Weil Deligne WDRep   eq one of line 0f8b50478b0c
-- statement:
--   The P2 M Global Theory Weil Deligne WDRep   eq one of line 0f8b50478b0c construction uses the P2 M Global Theory Weil Deligne WDRep   eq one of line 0f8b50478b0c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/LpCharCompatibilities.lean#L74-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/LpCharCompatibilities.lean#L74-L87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_LpCharCompatibilities
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial TensorProduct Module
open GlobalTheory GlobalTheory.WeilDeligne
variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
variable {V V' V'' : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
  [AddCommGroup V''] [Module ℂ V''] [FiniteDimensional ℂ V'']
open GlobalTheory.WeilDeligne.WDRep

theorem P2M_GlobalTheory_WeilDeligne_WDRep___eq_one_of_line_0f8b50478b0c (c : WDRep h V') (hu : c.Unr) (hd : finrank ℂ V' = 1)
    (hroot : (c.ρ (frob h)).charpoly.IsRoot 1) (σ : Weil h) : c.ρ σ = 1 := by sorry

alias «GlobalTheory».«WeilDeligne».«WDRep».«ρ_eq_one_of_line» := P2M_GlobalTheory_WeilDeligne_WDRep___eq_one_of_line_0f8b50478b0c
