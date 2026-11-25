-- Prove2me | Theorems.Thm_PositivityTheory_KReal_nontrivial_of_form
-- name    : PositivityTheory.KReal.nontrivial_of_form
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:35:05.367629+00:00
-- url     : https://prove2.me/theorems/6183cb84-5a01-4d6d-b18d-32e4a9ffde06
-- title:
--   KReal: nontrivial of form
-- statement:
--   The KReal construction uses the nontrivial of form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreDelta.lean#L278-L307
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreDelta.lean#L278-L307

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDefs
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDelta
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
open scoped InnerProductSpace TensorProduct
open PositivityTheory PositivityTheory.KReal
open Delta

theorem PositivityTheory.KReal.nontrivial_of_form {p q r s : ℕ} (c : ℂ) (b : Pol p q r 0 →ₗ[ℂ] Pol p q 0 s →ₗ[ℂ] ℂ)
    (hb : ∀ Z u v, b (fockAct1 p q r 0 Z u) v + b u (fockAct1 p q 0 s Z v) = c * Z.trace * b u v)
    (u0 : Pol p q r 0) (v0 : Pol p q 0 s) (hne : b u0 v0 ≠ 0) : Nontrivial (ThC p q r s c) := by sorry
