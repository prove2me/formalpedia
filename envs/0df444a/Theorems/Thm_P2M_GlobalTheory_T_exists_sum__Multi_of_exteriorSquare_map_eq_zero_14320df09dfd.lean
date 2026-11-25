-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exists_sum__Multi_of_exteriorSquare_map_eq_zero_14320df09dfd
-- name    : P2M_GlobalTheory_T_exists_sum__Multi_of_exteriorSquare_map_eq_zero_14320df09dfd
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T15:21:57.006791+00:00
-- url     : https://prove2.me/theorems/c41d6361-6ba7-4577-814f-312f008b68a0
-- title:
--   P2 M Global Theory T exists sum  Multi of exterior Square map eq zero 14320df09dfd: P2 M Global Theory T exists sum  Multi of exterior Square map eq zero 14320df09dfd
-- statement:
--   The P2 M Global Theory T exists sum  Multi of exterior Square map eq zero 14320df09dfd construction uses the P2 M Global Theory T exists sum  Multi of exterior Square map eq zero 14320df09dfd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExteriorSquareKerOfSurjectiveStatement.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExteriorSquareKerOfSurjectiveStatement.lean#L11-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExteriorSquareKerOfSurjective
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExteriorSquareKerOfSurjectiveStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_exists_sum__Multi_of_exteriorSquare_map_eq_zero_14320df09dfd : ∀ (R : Type) [CommRing R] (W M H : Type) [AddCommGroup W] [Module R W] [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H] (i : W →ₗ[R] M) (p : M →ₗ[R] H), Function.Surjective p → Function.Exact i p → ∀ t : ⋀[R]^2 M, exteriorPower.map 2 p t = 0 → ∃ (n : ℕ) (a : Fin n → M) (w : Fin n → W), t = ∑ k, exteriorPower.ιMulti R 2 ![a k, i (w k)] := by sorry

alias «GlobalTheory».«T».«exists_sum_ιMulti_of_exteriorSquare_map_eq_zero» := P2M_GlobalTheory_T_exists_sum__Multi_of_exteriorSquare_map_eq_zero_14320df09dfd
