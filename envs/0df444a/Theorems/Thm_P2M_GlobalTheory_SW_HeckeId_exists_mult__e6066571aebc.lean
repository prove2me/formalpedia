-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SW_HeckeId_exists_mult__e6066571aebc
-- name    : P2M_GlobalTheory_SW_HeckeId_exists_mult__e6066571aebc
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:09:35.659886+00:00
-- url     : https://prove2.me/theorems/9379dae3-0bb3-4f2c-9bfa-8c31ecdc5d9f
-- title:
--   P2 M Global Theory SW Hecke Id exists mult  e6066571aebc: P2 M Global Theory SW Hecke Id exists mult  e6066571aebc
-- statement:
--   The P2 M Global Theory SW Hecke Id exists mult  e6066571aebc construction uses the P2 M Global Theory SW Hecke Id exists mult  e6066571aebc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/HeckeRelationAdmissibleFamilyPointwise.lean#L548-L561
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/HeckeRelationAdmissibleFamilyPointwise.lean#L548-L561

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
omit [IsCMField E]

theorem P2M_GlobalTheory_SW_HeckeId_exists_mult__e6066571aebc {M R q : ℕ} (hR : 0 < R) (hq : q.Coprime (R * M)) {𝔛 : Lt E N}
    (h : Agree (R * M) 𝔛 (stdL E N)) :
    ∃ s : ℕ, s ≡ 1 [MOD R ^ 2] ∧ ∀ v ∈ stdL E N, ∃ ξ ∈ 𝔛, (s : E) • v = (q : E) • ξ := by sorry

alias «GlobalTheory».«SW».«HeckeId».«exists_mult'» := P2M_GlobalTheory_SW_HeckeId_exists_mult__e6066571aebc
