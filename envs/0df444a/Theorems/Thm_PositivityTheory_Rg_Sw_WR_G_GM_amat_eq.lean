-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_GM_amat_eq
-- name    : PositivityTheory.Rg.Sw.WR.G.GM.amat_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:50:21.219231+00:00
-- url     : https://prove2.me/theorems/cccb18c0-b1f8-4f8c-b1a1-d962c2733715
-- title:
--   GM: amat eq
-- statement:
--   The GM construction uses the amat eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GaussM.lean#L118-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GaussM.lean#L118-L123

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GaussS
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GaussM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix MvPolynomial
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.G
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
open PositivityTheory.Rg.Sw.WR.G.GM

theorem PositivityTheory.Rg.Sw.WR.G.GM.amat_eq (ε : Fin m → Bool) (c s : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) (a : Fin m) :
    Amat ε c (s * c) b a = (c : ℂ) • (Mm ε s b a)ᵀ := by sorry
