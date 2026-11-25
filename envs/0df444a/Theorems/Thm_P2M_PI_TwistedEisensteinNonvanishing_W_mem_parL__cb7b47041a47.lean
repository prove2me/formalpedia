-- Prove2me | Theorems.Thm_P2M_PI_TwistedEisensteinNonvanishing_W_mem_parL__cb7b47041a47
-- name    : P2M_PI_TwistedEisensteinNonvanishing_W_mem_parL__cb7b47041a47
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:58:40.621727+00:00
-- url     : https://prove2.me/theorems/794814d7-7f14-4940-93fb-bee786f6ece1
-- title:
--   P2 M PI Twisted Eisenstein Nonvanishing W mem par L  cb7b47041a47: P2 M PI Twisted Eisenstein Nonvanishing W mem par L  cb7b47041a47
-- statement:
--   The P2 M PI Twisted Eisenstein Nonvanishing W mem par L  cb7b47041a47 construction uses the P2 M PI Twisted Eisenstein Nonvanishing W mem par L  cb7b47041a47 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/JacobianTransformationLaw.lean#L53-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/JacobianTransformationLaw.lean#L53-L58

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

theorem P2M_PI_TwistedEisensteinNonvanishing_W_mem_parL__cb7b47041a47 {q kj n c : ℕ} (x : Sp E (n + c)) :
    x ∈ parL P q kj n c ↔ ∀ l : Fin (n + c), IntAt P (((q : E) ^ (if kj ≤ l.1 ∧ l.1 < n then (1 : ℤ) else 0))⁻¹ * x l) := by sorry

alias «PI».«TwistedEisensteinNonvanishing».«W».«mem_parL'» := P2M_PI_TwistedEisensteinNonvanishing_W_mem_parL__cb7b47041a47
