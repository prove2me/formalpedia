-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_nA_ip_U
-- name    : ReciprocityTheory.ChartRestriction.G.I2.nA_ip_U
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:31:39.467439+00:00
-- url     : https://prove2.me/theorems/dc17150d-5324-54a3-99cc-a7eb96b50913
-- title:
--   I2: n A ip U
-- statement:
--   The I2 construction uses the n A ip U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/LemmaNA.lean#L100-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/LemmaNA.lean#L100-L114

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

theorem ReciprocityTheory.ChartRestriction.G.I2.nA_ip_U (q : ℕ) {n : ℕ} (a : Fin n → Vsp X.dim) (F G : (Fin n → Vsp X.dim) → ℂ)
    (v : Fin n → Vsp X.dim) :
    X.U q a F v * (starRingEnd ℂ) (X.U q a G v) * ((Real.exp (-(q * Real.pi) * (HC v v).re) : ℝ) : ℂ) =
      F (v - a) * (starRingEnd ℂ) (G (v - a)) *
        ((Real.exp (-(q * Real.pi) * (HC (v - a) (v - a)).re) : ℝ) : ℂ) := by sorry
