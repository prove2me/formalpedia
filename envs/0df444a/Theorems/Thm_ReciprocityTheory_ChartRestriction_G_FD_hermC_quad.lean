-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_quad
-- name    : ReciprocityTheory.ChartRestriction.G.FD.hermC_quad
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:17:06.004084+00:00
-- url     : https://prove2.me/theorems/e725cbde-2fff-47b5-8e92-da471598e0bd
-- title:
--   FD: herm C quad
-- statement:
--   The FD construction uses the herm C quad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LminorSubmatrixCastSucc.lean#L182-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LminorSubmatrixCastSucc.lean#L182-L191

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open Matrix NumberField
open scoped ComplexOrder ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.FD.hermC_quad (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {n : ℕ} (γ : Fin n → ℂ)
    (f : Fin n → Fin r → ℂ) :
    hermC τ G (∑ a, γ a • f a) (∑ b, γ b • f b) =
      ∑ a, ∑ b, γ a * hermC τ G (f a) (f b) * conj (γ b) := by sorry
