-- Prove2me | Theorems.Thm_P2M_PI_TwNormLat_W_one_notMem__7f2d7b4a1758
-- name    : P2M_PI_TwNormLat_W_one_notMem__7f2d7b4a1758
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:15:46.087349+00:00
-- url     : https://prove2.me/theorems/33ce3016-5154-4a34-b168-9f745ba996a1
-- title:
--   P2 M PI Tw Norm Lat W one not Mem  7f2d7b4a1758: P2 M PI Tw Norm Lat W one not Mem  7f2d7b4a1758
-- statement:
--   The P2 M PI Tw Norm Lat W one not Mem  7f2d7b4a1758 construction uses the P2 M PI Tw Norm Lat W one not Mem  7f2d7b4a1758 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedNormLattice/UniformContinuityGaloisGroup.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedNormLattice/UniformContinuityGaloisGroup.lean#L11-L12

import Definitions.Def_Formalism_PeriodIntegrals_TwNormLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_UniformContinuityGaloisGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open PI PI.TwNormLat PI.TwNormLat.W
variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))

theorem P2M_PI_TwNormLat_W_one_notMem__7f2d7b4a1758 : (1 : 𝓞 E) ∉ P.asIdeal := by sorry

alias «PI».«TwNormLat».«W».«one_notMem'» := P2M_PI_TwNormLat_W_one_notMem__7f2d7b4a1758
