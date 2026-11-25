-- Prove2me | Theorems.Thm_PositivityTheory_KReal_fock_inner_adjoint_first
-- name    : PositivityTheory.KReal.fock_inner_adjoint_first
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:30:22.822958+00:00
-- url     : https://prove2.me/theorems/1d51bf68-2b95-5b1f-8c7d-4c751a0f7da9
-- title:
--   KReal: fock inner adjoint first
-- statement:
--   The KReal construction uses the fock inner adjoint first property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreLie.lean#L125-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreLie.lean#L125-L131

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCyc
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreLie
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
variable {p q r s : ℕ}

theorem PositivityTheory.KReal.fock_inner_adjoint_first (a b : Ix p q) (u v : Pol p q r s) :
    fockInner (fockAct1 p q r s (Eab a b) u) v = epsB a b * fockInner u (fockAct1 p q r s (Eab b a) v) := by sorry
