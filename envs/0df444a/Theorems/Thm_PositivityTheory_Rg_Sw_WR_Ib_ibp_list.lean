-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_Ib_ibp_list
-- name    : PositivityTheory.Rg.Sw.WR.Ib.ibp_list
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:01:40.946304+00:00
-- url     : https://prove2.me/theorems/5312a08f-3608-4d65-9342-70de50445fd8
-- title:
--   Ib: ibp list
-- statement:
--   The Ib construction uses the ibp list property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/IntegrableOfBound.lean#L185-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/IntegrableOfBound.lean#L185-L201

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

theorem PositivityTheory.Rg.Sw.WR.Ib.ibp_list {f : E n → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (t : ℝ) (β : E n)
    (hb : ∀ L : List (Fin n × Fin n), ∃ h : E n → ℝ, Integrable h ∧
      ∀ y, ‖L.foldr (fun kl g => Dkl kl.1 kl.2 g) f y‖ ≤ h y) (L : List (Fin n × Fin n)) :
    ∫ y, L.foldr (fun kl g => Dkl kl.1 kl.2 g) f y * chr t β y =
      (L.map fun kl => Complex.I * t * herm β kl.1 kl.2).prod * ∫ y, f y * chr t β y := by sorry
