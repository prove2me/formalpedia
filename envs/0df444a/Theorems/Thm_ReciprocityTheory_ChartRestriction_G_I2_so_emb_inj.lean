-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_so_emb_inj
-- name    : ReciprocityTheory.ChartRestriction.G.I2.so_emb_inj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:58:29.734777+00:00
-- url     : https://prove2.me/theorems/391b5ca0-bcc3-4931-9ff4-4f4086386638
-- title:
--   I2: so emb inj
-- statement:
--   The I2 construction uses the so emb inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitOA.lean#L92-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitOA.lean#L92-L107

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitOA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField
noncomputable section
variable {E : Type} [Field E] [NumberField E]

theorem ReciprocityTheory.ChartRestriction.G.I2.so_emb_inj (v : (E →+* ℂ) → ℂ)
    (h : ∀ i, ∑ σ : E →+* ℂ, v σ * σ (RingOfIntegers.basis E i : E) = 0) : v = 0 := by sorry
