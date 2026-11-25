-- Prove2me | Theorems.Thm_UpperTheory_Lit_Mix_multiProd_at
-- name    : UpperTheory.Lit.Mix.multiProd_at
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T14:45:38.434796+00:00
-- url     : https://prove2.me/theorems/dc3075d3-d85d-4b9e-a9c8-6142a74de2b6
-- title:
--   Mix: multi Prod at
-- statement:
--   The Mix construction uses the multi Prod at property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ThetaCorrespondence/GeneralLinearGroups/MultiAt.lean#L52-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ThetaCorrespondence/GeneralLinearGroups/MultiAt.lean#L52-L64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsIrreducibleIffOfLinearEquiv
import Definitions.Def_Development_AutomorphicArithmetic_ThetaCorrespondence_GeneralLinearGroups_MultiAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.MultiIrr ValuativeRel Matrix
open scoped TensorProduct
open UpperTheory UpperTheory.Lit UpperTheory.Lit.Mix
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem UpperTheory.Lit.Mix.multiProd_at (H : TwoAt k) {s : ℕ} :
    ∀ {m : Fin s → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {n : Type} [Fintype n] [DecidableEq n]
    (e : (Σ i, m i) ≃ n) {X : Fin s → Type} [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
    {σ : ∀ i, Representation ℂ (GL (m i) k) (X i)}, (∀ i, IsSmooth (σ i)) → (∀ i, (σ i).IsIrreducible) →
    (∀ i, IsUnitarisable (σ i)) → (multiProd e σ).IsIrreducible := by sorry
