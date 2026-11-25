-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_dmin_line
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.dmin_line
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:05:26.112639+00:00
-- url     : https://prove2.me/theorems/1b8c1511-2173-598f-8a07-3c84a3b3569f
-- title:
--   Curv Pf: dmin line
-- statement:
--   The Curv Pf construction uses the dmin line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/ArakelovInstances/DetSubMapConj.lean#L57-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/ArakelovInstances/DetSubMapConj.lean#L57-L90

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_LminorMapConj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_DetSubMapConj
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
open Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.dmin_line (x0 b : Frame X.Ψ r) (hb : b ∈ Bor X.Ψ r) (z u : V (nd X)) (τ : X.Ψ)
    (hgram : gram τ.1 X.Gm (mat (rmul (cpt X x0 z) b) τ) = diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ))
    (ζ : ℂ) (k : Fin (r + 1)) :
    dmin X.Gm (cpt X x0 (z + ζ • u)) τ k =
      ((mat b τ)⁻¹.submatrix (Fin.castLE (Nat.le_of_lt_succ k.isLt)) (Fin.castLE (Nat.le_of_lt_succ k.isLt))).det *
        starRingEnd ℂ (Gz (Nat.le_of_lt_succ k.isLt) (Dsg X) (Yd X b z u τ) ζ).det *
        starRingEnd ℂ ((mat b τ)⁻¹.submatrix (Fin.castLE (Nat.le_of_lt_succ k.isLt))
          (Fin.castLE (Nat.le_of_lt_succ k.isLt))).det := by sorry
