-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CentralExponent_val_emb__scalar_9fecca134d59
-- name    : P2M_GlobalTheory_CentralExponent_val_emb__scalar_9fecca134d59
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:11:35.652998+00:00
-- url     : https://prove2.me/theorems/b4d5e0aa-ecad-4669-b175-89fbf33055a1
-- title:
--   P2 M Global Theory Central Exponent val emb  scalar 9fecca134d59: P2 M Global Theory Central Exponent val emb  scalar 9fecca134d59
-- statement:
--   The P2 M Global Theory Central Exponent val emb  scalar 9fecca134d59 construction uses the P2 M Global Theory Central Exponent val emb  scalar 9fecca134d59 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CentralExponentBoundOver.lean#L188-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CentralExponentBoundOver.lean#L188-L196

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_IrreducibleTensorCharacter
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfIsIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CentralExponentBoundOver
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.StepData ValuativeRel Matrix Topology Filter
open scoped TensorProduct
open GlobalTheory GlobalTheory.CentralExponent
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]
variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem P2M_GlobalTheory_CentralExponent_val_emb__scalar_9fecca134d59 (e : a ⊕ b ≃ n) (z : kˣ) :
    (emb₂ k e (GeneralLinearGroup.scalar a z, 1)).val =
      diagonal fun i => if (e.symm i).isLeft then (z : k) else 1 := by sorry

alias «GlobalTheory».«CentralExponent».«val_emb₂_scalar» := P2M_GlobalTheory_CentralExponent_val_emb__scalar_9fecca134d59
