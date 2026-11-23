-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_Ib_contDiff_foldr
-- name    : PositivityTheory.Rg.Sw.WR.Ib.contDiff_foldr
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:51:12.453136+00:00
-- url     : https://prove2.me/theorems/5addeadb-f7ea-4041-b7ef-aed24bcf6b30
-- title:
--   Ib: cont Diff foldr
-- statement:
--   The Ib construction uses the cont Diff foldr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/IntegrableOfBound.lean#L179-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/IntegrableOfBound.lean#L179-L183

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_IntegrableOfBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Ib
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.WR.Ib.contDiff_foldr {f : E n → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (L : List (Fin n × Fin n)) :
    ContDiff ℝ (⊤ : ℕ∞) (L.foldr (fun kl g => Dkl kl.1 kl.2 g) f) := by sorry
