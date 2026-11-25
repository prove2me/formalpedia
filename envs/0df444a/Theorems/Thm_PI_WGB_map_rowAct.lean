-- Prove2me | Theorems.Thm_PI_WGB_map_rowAct
-- name    : PI.WGB.map_rowAct
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:47:05.116415+00:00
-- url     : https://prove2.me/theorems/c6496bde-3f0d-448a-ac57-69e5aa2a50a8
-- title:
--   WGB: map row Act
-- statement:
--   The WGB construction uses the map row Act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/AevalScaleMonomial.lean#L29-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/AevalScaleMonomial.lean#L29-L37

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_FockFRowActRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_AevalScaleMonomial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGB
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
open Formalism.REAL (fockF)

theorem PI.WGB.map_rowAct {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {r c : ℕ}
    (A : Matrix (Fin r) (Fin r) R) (p : MvPolynomial (Fin r × Fin c) R) :
    map φ (rowAct R A p) = rowAct S (A.map φ) (map φ p) := by sorry
