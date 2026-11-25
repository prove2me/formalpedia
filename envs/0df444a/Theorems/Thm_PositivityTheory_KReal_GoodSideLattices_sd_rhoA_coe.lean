-- Prove2me | Theorems.Thm_PositivityTheory_KReal_GoodSideLattices_sd_rhoA_coe
-- name    : PositivityTheory.KReal.GoodSideLattices.sd_rhoA_coe
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:30:34.067887+00:00
-- url     : https://prove2.me/theorems/06f770bb-3885-5083-88a0-ba36c65f8af1
-- title:
--   Good Side Lattices: sd rho A coe
-- statement:
--   The Good Side Lattices construction uses the sd rho A coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreSide.lean#L93-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreSide.lean#L93-L97

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreStar
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreGen
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreSide
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.KReal
open PositivityTheory.KReal.GoodSideLattices
variable {p q r s : ℕ}

theorem PositivityTheory.KReal.GoodSideLattices.sd_rhoA_coe (τ : ℂ) (d : ℕ) {a b : Ix r s} (hab : sameBlock a b) (u : sd_hA p q r s d) :
    (sd_rhoA p q r s τ d a b u : FV p q r s) = sd_fvTw p q r s τ (Eab a b) u := by sorry
