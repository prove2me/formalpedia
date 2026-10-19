-- Prove2me | Theorems.Thm_SoficGroups_CompletedSourceFinalGeneratorTransfer_twiceCompleted_sourceGenerator_normalizedHamming_tendsto_zero
-- name    : SoficGroups.CompletedSourceFinalGeneratorTransfer.twiceCompleted_sourceGenerator_normalizedHamming_tendsto_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:30.418361+00:00
-- url     : https://prove2.me/theorems/27a3736b-8fb9-4883-82d8-24ca3340ddb7
-- title:
--   SoficGroups.CompletedSourceFinalGeneratorTransfer.twiceCompleted_sourceGenerator_normalizedHamming_tendsto_zero
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.CompletedSourceFinalGeneratorTransfer
open Filter Topology
open SoficGroups.MatchedComponentCompletion
open SoficGroups.CompletedSourceChosenWordRestrictionTransfer

theorem SoficGroups.CompletedSourceFinalGeneratorTransfer.twiceCompleted_sourceGenerator_normalizedHamming_tendsto_zero
    (V : ℕ → Type*) [∀ n, Fintype (V n)]
    [∀ n, DecidableEq (V n)]
    {ι J : Type*}
    (σ : (n : ℕ) → ι → Equiv.Perm (V n))
    (p : (n : ℕ) → J → Equiv.Perm (V n))
    (s : ι → J)
    (P : (n : ℕ) → Finset (V n))
    (D : (n : ℕ) → Finset {x : V n // x ∈ P n})
    (τ : (n : ℕ) → (i : ι) →
      Equiv.Perm
        {x : {x : V n // x ∈ P n} //
          x ∈ (Finset.univ \ D n :
            Finset {x : V n // x ∈ P n})})
    (hsource : ∀ n i, σ n i = p n (s i))
    (hagrees : ∀ n i,
      ∀ x : {x : {x : V n // x ∈ P n} //
        x ∈ (Finset.univ \ D n :
          Finset {x : V n // x ∈ P n})},
        completedRestriction (σ n i) (P n) x.val ∈
          (Finset.univ \ D n :
            Finset {x : V n // x ∈ P n}) →
        (τ n i x).val =
          completedRestriction (σ n i) (P n) x.val)
    (hZ : ∀ n,
      (Finset.univ \ D n :
        Finset {x : V n // x ∈ P n}).Nonempty)
    (hdeleted : Tendsto
      (fun n => ((D n).card : ℝ) / (P n).card)
      atTop (nhds 0)) :
    ∀ i : ι,
      Tendsto
        (fun n =>
          SoficGroups.normalizedHamming
            (τ n i)
            (completedRestriction
              (completedRestriction (p n (s i)) (P n))
              (Finset.univ \ D n)))
        atTop (nhds 0) := by sorry
