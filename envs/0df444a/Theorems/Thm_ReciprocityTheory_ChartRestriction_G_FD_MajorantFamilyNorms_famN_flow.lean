-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantFamilyNorms_famN_flow
-- name    : ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.famN_flow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:16:20.667389+00:00
-- url     : https://prove2.me/theorems/57ce5dc2-cdaf-4f4f-aab2-63903202cfc3
-- title:
--   Majorant Family Norms: fam N flow
-- statement:
--   The Majorant Family Norms construction uses the fam N flow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MajorantFamilyNorms.lean#L42-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MajorantFamilyNorms.lean#L42-L58

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_GramFlowTransform
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantFamilyNorms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms
open Complex Matrix ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits ReciprocityTheory.ChartRestriction.G.FD.GramFlowTransform
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.famN_flow (e : X.Ψ → Fin r → ℂ) (s : X.Ψ → ℂ) (x : Frame X.Ψ r) (τ : X.Ψ) (i : ℕ)
    (h : i ≤ r) : famN (mat (X.flowV e s x) τ) i h =
      flw (-I * X.c τ * s τ) (e τ) τ.1 X.Gm (famN (mat x τ) i h) := by sorry
