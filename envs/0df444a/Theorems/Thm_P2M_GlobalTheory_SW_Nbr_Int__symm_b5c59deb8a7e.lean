-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SW_Nbr_Int__symm_b5c59deb8a7e
-- name    : P2M_GlobalTheory_SW_Nbr_Int__symm_b5c59deb8a7e
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:45:11.373851+00:00
-- url     : https://prove2.me/theorems/0ab8e7c0-eee3-4fef-a7ec-829b0138c4e5
-- title:
--   P2 M Global Theory SW Nbr Int  symm b5c59deb8a7e: P2 M Global Theory SW Nbr Int  symm b5c59deb8a7e
-- statement:
--   The P2 M Global Theory SW Nbr Int  symm b5c59deb8a7e construction uses the P2 M Global Theory SW Nbr Int  symm b5c59deb8a7e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/NeBotOfNorm.lean#L85-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/NeBotOfNorm.lean#L85-L88

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CycOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical nonZeroDivisors
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Nbr
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem P2M_GlobalTheory_SW_Nbr_Int__symm_b5c59deb8a7e {x y : Fin n → E} (h : Int' x y) : Int' y x := by sorry

alias «GlobalTheory».«SW».«Nbr».«Int'».«symm» := P2M_GlobalTheory_SW_Nbr_Int__symm_b5c59deb8a7e
