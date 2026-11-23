-- Prove2me | Theorems.Thm_P2M_PI_TwNormLat_W_mul_notMem__ff4d1c9ef9d9
-- name    : P2M_PI_TwNormLat_W_mul_notMem__ff4d1c9ef9d9
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:15:44.591984+00:00
-- url     : https://prove2.me/theorems/c2e1db48-460f-4c3c-9a0a-188c3367bccd
-- title:
--   P2 M PI Tw Norm Lat W mul not Mem  ff4d1c9ef9d9: P2 M PI Tw Norm Lat W mul not Mem  ff4d1c9ef9d9
-- statement:
--   The P2 M PI Tw Norm Lat W mul not Mem  ff4d1c9ef9d9 construction uses the P2 M PI Tw Norm Lat W mul not Mem  ff4d1c9ef9d9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedNormLattice/UniformContinuityGaloisGroup.lean#L14-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedNormLattice/UniformContinuityGaloisGroup.lean#L14-L15

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

theorem P2M_PI_TwNormLat_W_mul_notMem__ff4d1c9ef9d9 {s t : 𝓞 E} (hs : s ∉ P.asIdeal) (ht : t ∉ P.asIdeal) : s * t ∉ P.asIdeal := by sorry

alias «PI».«TwNormLat».«W».«mul_notMem'» := P2M_PI_TwNormLat_W_mul_notMem__ff4d1c9ef9d9
