-- Prove2me | Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_fIdx_inj
-- name    : PI.TwistedEisensteinNonvanishing.W.fIdx_inj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:42:45.628085+00:00
-- url     : https://prove2.me/theorems/932457f6-3a38-40c8-ae40-7b9bf531fb3a
-- title:
--   W: f Idx inj
-- statement:
--   The W construction uses the f Idx inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/JacobianTransformationLaw.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/JacobianTransformationLaw.lean#L18-L21

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

theorem PI.TwistedEisensteinNonvanishing.W.fIdx_inj {k₀ c n p p' : ℕ} (hp : p < n + c) (hp' : p' < n + c) (hk : k₀ ≤ n)
    (h : fIdx k₀ c n p = fIdx k₀ c n p') : p = p' := by sorry
