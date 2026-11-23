-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_QuadraticLatticeForms_ip_self
-- name    : ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.ip_self
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:17:37.67172+00:00
-- url     : https://prove2.me/theorems/675d9c88-4827-44bd-9658-f4a1563fbfd8
-- title:
--   Quadratic Lattice Forms: ip self
-- statement:
--   The Quadratic Lattice Forms construction uses the ip self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/QuadraticLatticeForms.lean#L64-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/QuadraticLatticeForms.lean#L64-L70

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealPlaceEmbeddings
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_IntegralModuleBases_DetToMatrixSq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_QuadraticLatticeForms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms
open Matrix NumberField Complex Module
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.ip_self (u : X.Ψ → Fin r → ℂ) : ip X u u = ∑ τ, X.c τ * ∑ a, ‖u τ a‖ ^ 2 := by sorry
