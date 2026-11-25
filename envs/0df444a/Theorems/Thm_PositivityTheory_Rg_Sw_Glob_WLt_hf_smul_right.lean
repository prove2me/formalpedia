-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_Glob_WLt_hf_smul_right
-- name    : PositivityTheory.Rg.Sw.Glob.WLt.hf_smul_right
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:55:18.389587+00:00
-- url     : https://prove2.me/theorems/35736355-f8d5-58d7-8756-62399c004e3a
-- title:
--   WLt: hf smul right
-- statement:
--   The WLt construction uses the hf smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GlobalGaussLaws/WittLtB.lean#L55-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GlobalGaussLaws/WittLtB.lean#L55-L59

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

theorem PositivityTheory.Rg.Sw.Glob.WLt.hf_smul_right {n : Type} [Fintype n] (G : Matrix n n E) (a : E) (x y : n → E) :
    hf G x (a • y) = FD.cc a * hf G x y := by sorry
