-- Prove2me | Theorems.Thm_PositivityTheory_KReal_harmonic_stable_lowering
-- name    : PositivityTheory.KReal.harmonic_stable_lowering
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:38:47.41358+00:00
-- url     : https://prove2.me/theorems/7535d1e2-637b-57f7-b494-2d11a5651683
-- title:
--   KReal: harmonic stable lowering
-- statement:
--   The KReal construction uses the harmonic stable lowering property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreHarm.lean#L306-L316
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreHarm.lean#L306-L316

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreLie
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreHarm
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
open Harm
variable {p q r s : ℕ}

theorem PositivityTheory.KReal.harmonic_stable_lowering {c d : Ix r s} (hcd : ¬ sameBlock c d) {g : Pol p q r s} (hg : g ∈ harm1 p q r s) :
    PI.FockOneDegW.lowOp (p := p) (q := q) c d g ∈ harm1 p q r s := by sorry
