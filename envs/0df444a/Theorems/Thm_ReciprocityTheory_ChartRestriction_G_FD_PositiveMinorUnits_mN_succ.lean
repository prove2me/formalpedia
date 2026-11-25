-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PositiveMinorUnits_mN_succ
-- name    : ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits.mN_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:16:58.148866+00:00
-- url     : https://prove2.me/theorems/c22a57a7-f649-45f8-9f5c-73341a4ab944
-- title:
--   Positive Minor Units: m N succ
-- statement:
--   The Positive Minor Units construction uses the m N succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/PositiveMinorUnits.lean#L41-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/PositiveMinorUnits.lean#L41-L47

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_GramDeterminantReal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PositiveMinorUnits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits
open Complex Matrix ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
variable {τ G} (hG : ∀ a b, τ (G b a) = conj (τ (G a b))) (p0 : ℕ) (hp0 : p0 ≤ r)
  (x : Matrix (Fin r) (Fin r) ℂ) (hx : x.det ≠ 0)
  (hsg : ∀ i (h : i ≤ r), 0 < psgn p0 i * (gramF τ G (famN x i h)).det.re)
  (e : Fin r → ℂ) (he : hermC τ G e e = 0)
include hsg
include hG

theorem ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits.mN_succ (i : ℕ) (h : i + 1 ≤ r) : mN τ G x e (i + 1) = mN τ G x e i +
    (hermC τ G (dv τ G (famN x (i + 1) h) e) (dv τ G (famN x (i + 1) h) e)).re := by sorry
