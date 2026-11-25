-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_Glob_WLt_hf_symm
-- name    : PositivityTheory.Rg.Sw.Glob.WLt.hf_symm
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:55:00.314669+00:00
-- url     : https://prove2.me/theorems/cb5f1f73-2908-5940-969f-fda10449a5a4
-- title:
--   WLt: hf symm
-- statement:
--   The WLt construction uses the hf symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GlobalGaussLaws/WittLtB.lean#L33-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GlobalGaussLaws/WittLtB.lean#L33-L41

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

theorem PositivityTheory.Rg.Sw.Glob.WLt.hf_symm {n : Type} [Fintype n] {G : Matrix n n E} (hG : ∀ a b, FD.cc (G a b) = G b a) (x y : n → E) :
    hf G y x = FD.cc (hf G x y) := by sorry
