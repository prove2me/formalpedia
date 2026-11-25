-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_line_levi
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.line_levi
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T01:32:27.560026+00:00
-- url     : https://prove2.me/theorems/579c7686-70c1-42cf-98fc-c1d14aee5353
-- title:
--   Curv Pf: line levi
-- statement:
--   The Curv Pf construction uses the line levi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/ArakelovInstances/LeviLogfk.lean#L42-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/ArakelovInstances/LeviLogfk.lean#L42-L90

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_LeviFinsetSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_LeviLogfk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
open Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates ReciprocityTheory.AnForm Filter Topology
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
  {x0 b : Frame X.Ψ r} {z u : V (nd X)}

theorem ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.line_levi (hb : b ∈ Bor X.Ψ r) (hgram : ∀ τ, gram τ.1 X.Gm (mat (rmul (cpt X x0 z) b) τ) =
      diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) (la : Wt X.Ψ r) :
    levi (fun v : Fin 1 → ℂ => -2 * Real.log (X.nfac la (cpt X x0 (z + lineL u v)))) 0 (fun _ => 1) =
      ∑ τ, ∑ i : Fin r, (la τ i : ℝ) * (Ck X b z u τ i.succ - Ck X b z u τ i.castSucc) := by sorry
