-- Prove2me | Theorems.Thm_PositivityTheory_KReal_kSt_cycK
-- name    : PositivityTheory.KReal.kSt_cycK
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:26:17.781126+00:00
-- url     : https://prove2.me/theorems/3754d550-9761-4c22-9d46-91bb58f224ab
-- title:
--   KReal: k St cyc K
-- statement:
--   The KReal construction uses the k St cyc K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCyc.lean#L200-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCyc.lean#L200-L203

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDefs
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCyc
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
variable {r s : ℕ}

theorem PositivityTheory.KReal.kSt_cycK {M : Type} [AddCommGroup M] [Module ℂ M] (ρ : Ix r s → Ix r s → Module.End ℂ M) (f : M) :
    KSt ρ (cycK ρ f) := by sorry
