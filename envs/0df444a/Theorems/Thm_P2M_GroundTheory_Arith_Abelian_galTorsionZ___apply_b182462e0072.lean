-- Prove2me | Theorems.Thm_P2M_GroundTheory_Arith_Abelian_galTorsionZ___apply_b182462e0072
-- name    : P2M_GroundTheory_Arith_Abelian_galTorsionZ___apply_b182462e0072
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:08:45.049353+00:00
-- url     : https://prove2.me/theorems/ca14b2c5-bf72-47f9-9f15-6258722111bd
-- title:
--   P2 M Ground Theory Arith Abelian gal Torsion Z   apply b182462e0072: P2 M Ground Theory Arith Abelian gal Torsion Z   apply b182462e0072
-- statement:
--   The P2 M Ground Theory Arith Abelian gal Torsion Z   apply b182462e0072 construction uses the P2 M Ground Theory Arith Abelian gal Torsion Z   apply b182462e0072 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/TorsionGalois.lean#L95-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/TorsionGalois.lean#L95-L98

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

theorem P2M_GroundTheory_Arith_Abelian_galTorsionZ___apply_b182462e0072 (n : ℕ) (σ : Gal(L/K))
    (P : torsionBy (W.baseChange L).toAffine.Point n) :
    (galTorsionZ K L W n).ρ σ P = galTorsionHom K L W n σ P := by sorry

alias «GroundTheory».«Arith».«Abelian».«galTorsionZ_ρ_apply» := P2M_GroundTheory_Arith_Abelian_galTorsionZ___apply_b182462e0072
