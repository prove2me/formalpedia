-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_QuadraticCoefficientForms_card_Psi_pos
-- name    : ReciprocityTheory.ChartRestriction.G.FD.QuadraticCoefficientForms.card_Psi_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:36:35.164185+00:00
-- url     : https://prove2.me/theorems/b726fe9f-d0d1-47c6-9072-d366e2e5fdbf
-- title:
--   Quadratic Coefficient Forms: card Psi pos
-- statement:
--   The Quadratic Coefficient Forms construction uses the card Psi pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/QuadraticCoefficientForms.lean#L93-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/QuadraticCoefficientForms.lean#L93-L103

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowIsotropicPairs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PackingSeparation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_QuadraticCoefficientForms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.QuadraticCoefficientForms
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate Classical
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.QuadraticCoefficientForms.card_Psi_pos : 0 < Fintype.card X.Ψ := by sorry
