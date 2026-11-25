-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_Glob_WLt_iso_diag
-- name    : PositivityTheory.Rg.Sw.Glob.WLt.iso_diag
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:59:46.302039+00:00
-- url     : https://prove2.me/theorems/c02bf9b5-5712-5120-9acc-3339c001c7be
-- title:
--   WLt: iso diag
-- statement:
--   The WLt construction uses the iso diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GlobalGaussLaws/WittLtA.lean#L44-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GlobalGaussLaws/WittLtA.lean#L44-L80

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_GlobalTheta_HermitianHassePrincipleHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsZeroCoordNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_PosIndexMapEqCardOfCongrDiagonal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GlobalGaussLaws_WittLtA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix NumberField
open scoped ComplexConjugate
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.Glob PositivityTheory.Rg.Sw.Glob.WLt
open ReciprocityTheory.ChartRestriction.G
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem PositivityTheory.Rg.Sw.Glob.WLt.iso_diag {r : ℕ} (g : Fin (r + 1) → E) (hr : 2 ≤ r) (hg : ∀ i, FD.cc (g i) = g i) (hg0 : ∀ i, g i ≠ 0)
    (hs : ∀ τ : E →+* ℂ, (∃ i, 0 < (τ (g i)).re) ∧ (∃ j, (τ (g j)).re < 0)) :
    ∃ z : Fin (r + 1) → E, z ≠ 0 ∧ z ⬝ᵥ diagonal g *ᵥ (FD.cc ∘ z) = 0 := by sorry
