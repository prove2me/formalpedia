-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_sumBd_frame
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.sumBd_frame
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:00:40.7809+00:00
-- url     : https://prove2.me/theorems/51a27160-0f1f-4eb2-aa4c-db0408484deb
-- title:
--   Up: sum Bd frame
-- statement:
--   The Up construction uses the sum Bd frame property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/SumBoundStatementPfA.lean#L237-L272
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/SumBoundStatementPfA.lean#L237-L272

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatementPfA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up
open Matrix Topology Filter
open scoped Matrix ComplexOrder ENNReal
noncomputable section
variable {p q : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.sumBd_frame {Z : Matrix (Fin p) (Fin q) ℂ} (hZ : (1 - Z * Zᴴ).PosDef) :
    ∃ G : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ, IsUpq G ∧
      ∀ g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ, IsUpq g → ∀ s : ℝ,
        dpow (mob g Z) s = ((Complex.normSq (det (g * G).toBlocks₂₂))⁻¹) ^ s := by sorry
