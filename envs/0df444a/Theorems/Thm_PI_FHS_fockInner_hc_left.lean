-- Prove2me | Theorems.Thm_PI_FHS_fockInner_hc_left
-- name    : PI.FHS.fockInner_hc_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:46.040647+00:00
-- url     : https://prove2.me/theorems/d7347088-568b-476a-b9a6-af23a857c1d7
-- title:
--   FHS: fock Inner hc left
-- statement:
--   The FHS construction uses the fock Inner hc left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/FockInnerSelfReNonneg.lean#L233-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/FockInnerSelfReNonneg.lean#L233-L247

import Definitions.Def_Formalism_PeriodIntegrals_JointBlockShapes_MinusPart
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_FockInnerSelfReNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PI PI.FHS
variable {σ : Type*}

theorem PI.FHS.fockInner_hc_left {n : ℕ} (P Q : MvPolynomial σ ℂ) (hQ : Q ∈ FockH1Action.homog σ n) :
    FockH1Action.fockInner (homogeneousComponent n P) Q = FockH1Action.fockInner P Q := by sorry
