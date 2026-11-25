-- Prove2me | Theorems.Thm_P2M_PositivityTheory_KReal_genG_le__7406e1e366d6
-- name    : P2M_PositivityTheory_KReal_genG_le__7406e1e366d6
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:09:18.785066+00:00
-- url     : https://prove2.me/theorems/2b7757fe-521c-5187-87ab-13ef3d1788ef
-- title:
--   P2 M Positivity Theory KReal gen G le  7406e1e366d6: P2 M Positivity Theory KReal gen G le  7406e1e366d6
-- statement:
--   The P2 M Positivity Theory KReal gen G le  7406e1e366d6 construction uses the P2 M Positivity Theory KReal gen G le  7406e1e366d6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreMain.lean#L95-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreMain.lean#L95-L97

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

theorem P2M_PositivityTheory_KReal_genG_le__7406e1e366d6 {act : Mat r s →ₗ[ℂ] Module.End ℂ M} {S N : Submodule ℂ M} (h1 : S ≤ N)
    (h2 : ∀ W, ∀ x ∈ N, act W x ∈ N) : genG act S ≤ N := by sorry

alias «PositivityTheory».«KReal».«genG_le'» := P2M_PositivityTheory_KReal_genG_le__7406e1e366d6
