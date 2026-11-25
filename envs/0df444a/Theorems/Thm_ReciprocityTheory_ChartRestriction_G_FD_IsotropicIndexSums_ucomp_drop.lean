-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_IsotropicIndexSums_ucomp_drop
-- name    : ReciprocityTheory.ChartRestriction.G.FD.IsotropicIndexSums.ucomp_drop
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:21:42.669402+00:00
-- url     : https://prove2.me/theorems/34fb19cf-4c56-5b4e-a04a-d4deb13fa869
-- title:
--   Isotropic Index Sums: ucomp drop
-- statement:
--   The Isotropic Index Sums construction uses the ucomp drop property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/IsotropicIndexSums.lean#L187-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/IsotropicIndexSums.lean#L187-L202

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ExistsPerpHermitianReduction
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_SemistableReduction_LatAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicIndexSums
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.IsotropicIndexSums
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.IsotropicIndexSums.ucomp_drop {x : Frame X.Ψ r} (hx : x ∈ X.dom) {ξ : Fin r → E} (hne : ξ ≠ 0)
    (v : Fin r → E) (e : E) (τ : X.Ψ) :
    X.ucomp x ξ (X.embV (v + e • ξ)) τ = X.ucomp x ξ (X.embV v) τ := by sorry
