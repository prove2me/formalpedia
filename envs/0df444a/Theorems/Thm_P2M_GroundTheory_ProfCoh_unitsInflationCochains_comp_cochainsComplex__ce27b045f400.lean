-- Prove2me | Theorems.Thm_P2M_GroundTheory_ProfCoh_unitsInflationCochains_comp_cochainsComplex__ce27b045f400
-- name    : P2M_GroundTheory_ProfCoh_unitsInflationCochains_comp_cochainsComplex__ce27b045f400
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:54:36.123737+00:00
-- url     : https://prove2.me/theorems/bedadfad-60ab-51c0-8238-98f8170c5d9a
-- title:
--   P2 M Ground Theory Prof Coh units Inflation Cochains comp cochains Complex  ce27b045f400: P2 M Ground Theory Prof Coh units Inflation Cochains comp cochains Complex  ce27b045f400
-- statement:
--   The P2 M Ground Theory Prof Coh units Inflation Cochains comp cochains Complex  ce27b045f400 construction uses the P2 M Ground Theory Prof Coh units Inflation Cochains comp cochains Complex  ce27b045f400 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GaloisCohomology/UnitsInflationCochainsFHomApply.lean#L124-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GaloisCohomology/UnitsInflationCochainsFHomApply.lean#L124-L129

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_Discrete
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_FixedField
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisCohomology_UnitsInflationCochainsFHomApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open CategoryTheory groupCohomology
universe u
variable (K L : Type u) [Field K] [Field L] [Algebra K L]
variable {K L}
variable [IsGalois K L]

theorem P2M_GroundTheory_ProfCoh_unitsInflationCochains_comp_cochainsComplex__ce27b045f400 (E : IntermediateField K L)
    [FiniteDimensional K E] [Normal K E] :
    unitsInflationCochains E ≫ cochainsComplexι (galUnits.{u} K L) =
      groupCohomology.cochainsMap (AlgEquiv.restrictNormalHom E) (unitsRestrictHom E) := by sorry

alias «GroundTheory».«ProfCoh».«unitsInflationCochains_comp_cochainsComplexι» := P2M_GroundTheory_ProfCoh_unitsInflationCochains_comp_cochainsComplex__ce27b045f400
