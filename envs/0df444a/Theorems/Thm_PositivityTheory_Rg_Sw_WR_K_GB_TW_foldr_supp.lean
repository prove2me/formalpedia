-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_TW_foldr_supp
-- name    : PositivityTheory.Rg.Sw.WR.K.GB.TW.foldr_supp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:54:04.661087+00:00
-- url     : https://prove2.me/theorems/b011c458-78c6-4dd9-a32a-e0c2a35a5ed2
-- title:
--   TW: foldr supp
-- statement:
--   The TW construction uses the foldr supp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBTwist.lean#L179-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBTwist.lean#L179-L186

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_Lagr
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBTwist
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.K PositivityTheory.Rg.Sw.WR.K.GB
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
open PositivityTheory.Rg.Sw.WR.K.GB.TW
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.WR.K.GB.TW.foldr_supp (f : Fin n → Fin n) : ∀ (l : List (Fin n)) (c : ℕ → E n → ℂ) (M : ℕ),
    (∀ j, M ≤ j → c j = 0) → ∀ j, M + l.length ≤ j → (l.foldr (fun k c' => TD k (f k) c') c) j = 0
  := by sorry
