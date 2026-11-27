-- Prove2me | Theorems.Thm_P2M_GroundTheory_Arith_Abelian_galPointsZ___apply_44b91bf63eb5
-- name    : P2M_GroundTheory_Arith_Abelian_galPointsZ___apply_44b91bf63eb5
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:07:32.707558+00:00
-- url     : https://prove2.me/theorems/d581536d-3482-5ee7-be91-25bbddb65d78
-- title:
--   P2 M Ground Theory Arith Abelian gal Points Z   apply 44b91bf63eb5: P2 M Ground Theory Arith Abelian gal Points Z   apply 44b91bf63eb5
-- statement:
--   The P2 M Ground Theory Arith Abelian gal Points Z   apply 44b91bf63eb5 construction uses the P2 M Ground Theory Arith Abelian gal Points Z   apply 44b91bf63eb5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/TorsionGalois.lean#L87-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/TorsionGalois.lean#L87-L89

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

theorem P2M_GroundTheory_Arith_Abelian_galPointsZ___apply_44b91bf63eb5 (σ : Gal(L/K)) (P : (W.baseChange L).toAffine.Point) :
    (galPointsZ K L W).ρ σ P = galPointsHom K L W σ P := by sorry

alias «GroundTheory».«Arith».«Abelian».«galPointsZ_ρ_apply» := P2M_GroundTheory_Arith_Abelian_galPointsZ___apply_44b91bf63eb5
