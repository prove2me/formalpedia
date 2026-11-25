-- Prove2me | Theorems.Thm_PositivityTheory_KReal_hwK_of_hwSub
-- name    : PositivityTheory.KReal.hwK_of_hwSub
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:32:35.836802+00:00
-- url     : https://prove2.me/theorems/395cf00a-6e0a-4f04-ba9c-5a96745c314b
-- title:
--   KReal: hw K of hw Sub
-- statement:
--   The KReal construction uses the hw K of hw Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreLie.lean#L145-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreLie.lean#L145-L147

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

theorem PositivityTheory.KReal.hwK_of_hwSub {m n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] {act : Mat m n →ₗ[ℂ] Module.End ℂ V}
    {μ : Ix m n → ℚ} {v : V} : v ∈ hwSub act μ ↔ HwK (units act) μ v := by sorry
