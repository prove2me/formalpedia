-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SW_HeckeId_sum_ite__fd2c2018495e
-- name    : P2M_GlobalTheory_SW_HeckeId_sum_ite__fd2c2018495e
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:09:21.166826+00:00
-- url     : https://prove2.me/theorems/2a8cd6e4-c722-4aec-a331-2adddcc07925
-- title:
--   P2 M Global Theory SW Hecke Id sum ite  fd2c2018495e: P2 M Global Theory SW Hecke Id sum ite  fd2c2018495e
-- statement:
--   The P2 M Global Theory SW Hecke Id sum ite  fd2c2018495e construction uses the P2 M Global Theory SW Hecke Id sum ite  fd2c2018495e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/HeckeRelationAdmissibleFamilyPointwise.lean#L541-L545
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/HeckeRelationAdmissibleFamilyPointwise.lean#L541-L545

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CardKerMatrixFiniteField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HeckeRelationAdmissibleFamilyPointwise
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
open scoped TensorProduct LinearAlgebra.Projectivization
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HeckeId
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ}
open Nbr
variable {X : Type} [AddCommGroup X] [Module (𝓞 E) X]

theorem P2M_GlobalTheory_SW_HeckeId_sum_ite__fd2c2018495e {A : ℕ} (p : Fin A → Prop) [DecidablePred p] (c : ℂ) (f : Fin A → ℂ)
    (hf : ∀ i, f i = if p i then c else 0) : ∑ i, f i = ({i | p i}.ncard : ℂ) * c := by sorry

alias «GlobalTheory».«SW».«HeckeId».«sum_ite'» := P2M_GlobalTheory_SW_HeckeId_sum_ite__fd2c2018495e
