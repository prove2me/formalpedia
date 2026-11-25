-- Prove2me | Theorems.Thm_P2M_PositivityTheory_KReal_le_genG__33d9f57319d5
-- name    : P2M_PositivityTheory_KReal_le_genG__33d9f57319d5
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:08:12.641551+00:00
-- url     : https://prove2.me/theorems/bfcdc9ba-9141-5eef-a982-a8af4ff58945
-- title:
--   P2 M Positivity Theory KReal le gen G  33d9f57319d5: P2 M Positivity Theory KReal le gen G  33d9f57319d5
-- statement:
--   The P2 M Positivity Theory KReal le gen G  33d9f57319d5 construction uses the P2 M Positivity Theory KReal le gen G  33d9f57319d5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreMain.lean#L92-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreMain.lean#L92-L93

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasGl
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreMain
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
variable {r s : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem P2M_PositivityTheory_KReal_le_genG__33d9f57319d5 (act : Mat r s →ₗ[ℂ] Module.End ℂ M) (S : Submodule ℂ M) : S ≤ genG act S := by sorry

alias «PositivityTheory».«KReal».«le_genG'» := P2M_PositivityTheory_KReal_le_genG__33d9f57319d5
