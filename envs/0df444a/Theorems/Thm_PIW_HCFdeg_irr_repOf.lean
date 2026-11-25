-- Prove2me | Theorems.Thm_PIW_HCFdeg_irr_repOf
-- name    : PIW.HCFdeg.irr_repOf
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:50:31.509323+00:00
-- url     : https://prove2.me/theorems/7f416470-37e3-4587-a004-b44a06116348
-- title:
--   HCFdeg: irr rep Of
-- statement:
--   The HCFdeg construction uses the irr rep Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalDegreeSquareIntegrable/FormalDegreeOrthogonality.lean#L20-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalDegreeSquareIntegrable/FormalDegreeOrthogonality.lean#L20-L27

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_FormalDegreeFromOrthogonality
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_FormalDegreeOrthogonality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.HCFdeg
open MeasureTheory PI.UpqRep
open scoped InnerProductSpace

theorem PIW.HCFdeg.irr_repOf {n : ℕ} (ε : Fin n → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (h : IsCRepOn (UJset ε) σ)
    (hI : IsIrredOn (UJset ε) σ) : Irr (repOf ε σ h) := by sorry
