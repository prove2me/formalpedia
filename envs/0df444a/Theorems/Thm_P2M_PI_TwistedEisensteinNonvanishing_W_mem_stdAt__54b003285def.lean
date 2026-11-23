-- Prove2me | Theorems.Thm_P2M_PI_TwistedEisensteinNonvanishing_W_mem_stdAt__54b003285def
-- name    : P2M_PI_TwistedEisensteinNonvanishing_W_mem_stdAt__54b003285def
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:24:57.950919+00:00
-- url     : https://prove2.me/theorems/24219aa9-117b-433c-9ae0-f49c05e27900
-- title:
--   P2 M PI Twisted Eisenstein Nonvanishing W mem std At  54b003285def: P2 M PI Twisted Eisenstein Nonvanishing W mem std At  54b003285def
-- statement:
--   The P2 M PI Twisted Eisenstein Nonvanishing W mem std At  54b003285def construction uses the P2 M PI Twisted Eisenstein Nonvanishing W mem std At  54b003285def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/JacobianTransformationLaw.lean#L37-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/JacobianTransformationLaw.lean#L37-L38

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
variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}

theorem P2M_PI_TwistedEisensteinNonvanishing_W_mem_stdAt__54b003285def {n : ℕ} (v : Sp E n) : v ∈ stdAt E n P ↔ ∀ l, IntAt P (v l) := by sorry

alias «PI».«TwistedEisensteinNonvanishing».«W».«mem_stdAt'» := P2M_PI_TwistedEisensteinNonvanishing_W_mem_stdAt__54b003285def
