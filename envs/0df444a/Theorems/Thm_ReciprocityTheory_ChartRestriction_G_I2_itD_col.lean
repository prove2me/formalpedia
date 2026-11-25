-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_itD_col
-- name    : ReciprocityTheory.ChartRestriction.G.I2.itD_col
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:33:23.429471+00:00
-- url     : https://prove2.me/theorems/d25fba26-994a-5188-b154-a3bb41e6126f
-- title:
--   I2: it D col
-- statement:
--   The I2 construction uses the it D col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PolyDerivMonomialOne.lean#L101-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PolyDerivMonomialOne.lean#L101-L110

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivMonomialOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
noncomputable section
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem ReciprocityTheory.ChartRestriction.G.I2.itD_col {s : (Fin 1 → W) → ℂ} (hs : ContDiff ℂ (⊤ : ℕ∞) s) (l : List W) :
    itD (fun z : W => s (fun _ => z)) l 0 = iteratedFDeriv ℂ l.length s 0 (fun j _ => l.get j) := by sorry
