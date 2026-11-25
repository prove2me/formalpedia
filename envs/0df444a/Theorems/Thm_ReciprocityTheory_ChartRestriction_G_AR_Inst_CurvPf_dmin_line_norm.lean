-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_dmin_line_norm
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.dmin_line_norm
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:56:30.662906+00:00
-- url     : https://prove2.me/theorems/d9a2089e-728b-572f-bf65-824d35232aec
-- title:
--   Curv Pf: dmin line norm
-- statement:
--   The Curv Pf construction uses the dmin line norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/ArakelovInstances/LeviFinsetSum.lean#L81-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/ArakelovInstances/LeviFinsetSum.lean#L81-L95

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_DetSubMapConj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_LeviFinsetSum
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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
variable (x0 b : Frame X.Ψ r) (z u : V (nd X))
variable {X x0 b z u}

theorem ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.dmin_line_norm (hb : b ∈ Bor X.Ψ r) (hgram : ∀ τ, gram τ.1 X.Gm (mat (rmul (cpt X x0 z) b) τ) =
      diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) (v : Fin 1 → ℂ) (τ : X.Ψ) (k : Fin (r + 1)) :
    ‖dmin X.Gm (cpt X x0 (z + (v 0) • u)) τ k‖ =
      ‖((mat b τ)⁻¹.submatrix (Fin.castLE (Nat.le_of_lt_succ k.isLt))
        (Fin.castLE (Nat.le_of_lt_succ k.isLt))).det‖ ^ 2 * |fk X b z u τ k v| := by sorry
