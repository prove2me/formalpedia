-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_nA_ip_periodic
-- name    : ReciprocityTheory.ChartRestriction.G.I2.nA_ip_periodic
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:29:52.542071+00:00
-- url     : https://prove2.me/theorems/0c62e230-20b7-4b41-8ba5-d8c2cc12ab30
-- title:
--   I2: n A ip periodic
-- statement:
--   The I2 construction uses the n A ip periodic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/LemmaNA.lean#L143-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/LemmaNA.lean#L143-L162

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

theorem ReciprocityTheory.ChartRestriction.G.I2.nA_ip_periodic {q n : ℕ} {F G : (Fin n → Vsp X.dim) → ℂ} (hF : F ∈ X.Sec q n) (hG : G ∈ X.Sec q n)
    {γ : Fin n → Vsp X.dim} (hγ : ∀ k, γ k ∈ X.L) (v : Fin n → Vsp X.dim) :
    F (v + γ) * (starRingEnd ℂ) (G (v + γ)) *
        ((Real.exp (-(q * Real.pi) * (HC (v + γ) (v + γ)).re) : ℝ) : ℂ) =
      F v * (starRingEnd ℂ) (G v) * ((Real.exp (-(q * Real.pi) * (HC v v).re) : ℝ) : ℂ) := by sorry
