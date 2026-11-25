-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_DivLC_leadM_succ
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.DivLC.leadM_succ
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:17:14.053074+00:00
-- url     : https://prove2.me/theorems/f7ff2424-54ce-4b7a-9207-ac5b0a37fbf1
-- title:
--   Div LC: lead M succ
-- statement:
--   The Div LC construction uses the lead M succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/DivStatementPfLC.lean#L61-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/DivStatementPfLC.lean#L61-L87

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_DivStatementPfLB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_DivStatementPfLC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.DivLC
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
  Asymptotics ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ContDiff ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.DivLC.leadM_succ {n δ : ℕ} (s : Fin n → Frame X.Ψ r → ℂ) (w0 : Frame X.Ψ r → ℂ)
    (t : Fin δ → Frame X.Ψ r → ℂ) (T d : ℕ) (cc cc' cnew : (Fin n → ℕ) → Fin δ → ℂ)
    (h1 : ∀ α ∈ Finset.Nat.antidiagonalTuple n d, cc' α = cnew α)
    (h2 : ∀ α, α ∉ Finset.Nat.antidiagonalTuple n d → cc' α = cc α) (y : Frame X.Ψ r) :
    leadM X s w0 t T (d + 1) cc' y =
      leadM X s w0 t T d cc y + ∑ α ∈ Finset.Nat.antidiagonalTuple n d,
        ∑ k, cnew α k * monoM X s α y * w0 y ^ (T - d) * t k y := by sorry
