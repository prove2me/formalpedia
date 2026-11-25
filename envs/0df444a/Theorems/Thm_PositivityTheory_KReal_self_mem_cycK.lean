-- Prove2me | Theorems.Thm_PositivityTheory_KReal_self_mem_cycK
-- name    : PositivityTheory.KReal.self_mem_cycK
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:24:46.485322+00:00
-- url     : https://prove2.me/theorems/6b22f6ec-79e2-5d15-87b9-259b49f5d0af
-- title:
--   KReal: self mem cyc K
-- statement:
--   The KReal construction uses the self mem cyc K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCyc.lean#L196-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCyc.lean#L196-L198

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

theorem PositivityTheory.KReal.self_mem_cycK {M : Type} [AddCommGroup M] [Module ℂ M] (ρ : Ix r s → Ix r s → Module.End ℂ M) (f : M) :
    f ∈ cycK ρ f := by sorry
