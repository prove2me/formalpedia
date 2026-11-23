-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_nA_epsprod_norm
-- name    : ReciprocityTheory.ChartRestriction.G.I2.nA_epsprod_norm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:29:01.649545+00:00
-- url     : https://prove2.me/theorems/fd5e7c7f-e53b-47ec-aafa-3af5bdfb49db
-- title:
--   I2: n A epsprod norm
-- statement:
--   The I2 construction uses the n A epsprod norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/LemmaNA.lean#L137-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/LemmaNA.lean#L137-L141

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaNA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E] (X : PT E)

theorem ReciprocityTheory.ChartRestriction.G.I2.nA_epsprod_norm {n : ℕ} {γ : Fin n → Vsp X.dim} (hγ : ∀ k, γ k ∈ X.L) :
    ‖∏ k, (X.eps (γ k) : ℂ)‖ = 1 := by sorry
