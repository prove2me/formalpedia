-- Prove2me | Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_fIdx_D
-- name    : PI.TwistedEisensteinNonvanishing.W.fIdx_D
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:37:35.933522+00:00
-- url     : https://prove2.me/theorems/5d2d35af-0a26-5d9c-8d64-261f3e8c6cd2
-- title:
--   W: f Idx D
-- statement:
--   The W construction uses the f Idx D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/JacobianTransformationLaw.lean#L28-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/JacobianTransformationLaw.lean#L28-L31

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IsUnitRedP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_UniformContinuityGaloisGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_JacobianTransformationLaw
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Module
noncomputable section
open PI PI.TwistedEisensteinNonvanishing PI.TwistedEisensteinNonvanishing.W
open Loc LocE

theorem PI.TwistedEisensteinNonvanishing.W.fIdx_D {k₀ c n kj p : ℕ} (hk : k₀ ≤ kj) (hp1 : kj + c ≤ p) (hp2 : p < n + c) :
    kj ≤ fIdx k₀ c n p ∧ fIdx k₀ c n p < n := by sorry
