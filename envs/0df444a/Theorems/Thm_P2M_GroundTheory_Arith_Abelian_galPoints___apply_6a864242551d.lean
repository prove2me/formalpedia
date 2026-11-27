-- Prove2me | Theorems.Thm_P2M_GroundTheory_Arith_Abelian_galPoints___apply_6a864242551d
-- name    : P2M_GroundTheory_Arith_Abelian_galPoints___apply_6a864242551d
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:07:22.585035+00:00
-- url     : https://prove2.me/theorems/47b73729-703e-52e4-860b-32653e7596f5
-- title:
--   P2 M Ground Theory Arith Abelian gal Points   apply 6a864242551d: P2 M Ground Theory Arith Abelian gal Points   apply 6a864242551d
-- statement:
--   The P2 M Ground Theory Arith Abelian gal Points   apply 6a864242551d construction uses the P2 M Ground Theory Arith Abelian gal Points   apply 6a864242551d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/TorsionGalois.lean#L83-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/TorsionGalois.lean#L83-L85

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_Torsion
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_Discrete
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_FixedField
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_TorsionGalois
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open GroundTheory.ProfCoh IntermediateField AddSubgroup WeierstrassCurve
universe w u
variable (K L : Type u) [Field K] [Field L] [Algebra K L] [DecidableEq L] (W : WeierstrassCurve K)

theorem P2M_GroundTheory_Arith_Abelian_galPoints___apply_6a864242551d (σ : Gal(L/K)) (P : (W.baseChange L).toAffine.Point) :
    (galPoints.{w} K L W).ρ σ P = galPointsHom K L W σ P := by sorry

alias «GroundTheory».«Arith».«Abelian».«galPoints_ρ_apply» := P2M_GroundTheory_Arith_Abelian_galPoints___apply_6a864242551d
