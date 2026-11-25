-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_HSt_hasDerivAt_det_add
-- name    : PositivityTheory.Rg.Sw.HSt.hasDerivAt_det_add
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:54:46.467104+00:00
-- url     : https://prove2.me/theorems/3642c9dc-90b0-5c35-bd70-d68411f7f511
-- title:
--   HSt: has Deriv At det add
-- statement:
--   The HSt construction uses the has Deriv At det add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/CayleyCosetSums/HasDerivAtDetOneAdd.lean#L23-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/CayleyCosetSums/HasDerivAtDetOneAdd.lean#L23-L30

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_CayleyCosetSums_HasDerivAtDetOneAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Polynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.HSt

theorem PositivityTheory.Rg.Sw.HSt.hasDerivAt_det_add {ι : Type} [Fintype ι] [DecidableEq ι] (A X : Matrix ι ι ℂ) (hA : IsUnit A.det) :
    HasDerivAt (fun s : ℂ => (A + s • X).det) (A.det * (A⁻¹ * X).trace) 0 := by sorry
