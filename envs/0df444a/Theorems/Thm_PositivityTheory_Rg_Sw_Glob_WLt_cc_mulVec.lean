-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_Glob_WLt_cc_mulVec
-- name    : PositivityTheory.Rg.Sw.Glob.WLt.cc_mulVec
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:49:24.565428+00:00
-- url     : https://prove2.me/theorems/430659bf-1902-41a3-bbed-890e63cda248
-- title:
--   WLt: cc mul Vec
-- statement:
--   The WLt construction uses the cc mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GlobalGaussLaws/WittLtB.lean#L16-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GlobalGaussLaws/WittLtB.lean#L16-L19

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GlobalGaussLaws_WittLtA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GlobalGaussLaws_WittLtB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix NumberField GlobalTheory.Inertia
open scoped ComplexConjugate
noncomputable section
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.Glob PositivityTheory.Rg.Sw.Glob.WLt
open ReciprocityTheory.ChartRestriction.G
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem PositivityTheory.Rg.Sw.Glob.WLt.cc_mulVec {n m : Type} [Fintype n] [Fintype m] (P : Matrix n m E) (y : m → E) :
    FD.cc ∘ (P *ᵥ y) = P.map FD.cc *ᵥ (FD.cc ∘ y) := by sorry
