-- Prove2me | Theorems.Thm_SoficGroups_KunActualTwicePrunedFirstFactorRootBad_twiceCompleted_firstFactor_mul_normalizedHamming_tendsto_zero_of_canonical_matched
-- name    : SoficGroups.KunActualTwicePrunedFirstFactorRootBad.twiceCompleted_firstFactor_mul_normalizedHamming_tendsto_zero_of_canonical_matched
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:33.785013+00:00
-- url     : https://prove2.me/theorems/60420838-58cc-4c5a-a148-43ddbc9dca8a
-- title:
--   SoficGroups.KunActualTwicePrunedFirstFactorRootBad.twiceCompleted_firstFactor_mul_normalizedHamming_tendsto_zero_of_canonical_matched
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualTwicePrunedFirstFactorRootBad
open Filter Topology
open SoficGroups.MatchedComponentCompletion
open SoficGroups.MatchedComponentExitBudget
open SoficGroups.KunActualSoficRootRadius
open SoficGroups.CanonicalProductRadiusBadMatchedCapture
open SoficGroups.CompletedSourceFinalGeneratorTransfer
open scoped BigOperators Pointwise

theorem SoficGroups.KunActualTwicePrunedFirstFactorRootBad.twiceCompleted_firstFactor_mul_normalizedHamming_tendsto_zero_of_canonical_matched
    {K J : Type*} [Group K] [Group J]
    [DecidableEq K] [DecidableEq J]
    (A : SoficGroups.SoficApproximation (K × J))
    (S : Finset K) (hone : 1 ∈ S)
    (hsymmetric : ∀ a ∈ S, a⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set K) = ⊤)
    (F : Finset J) (ν : ℕ → ℕ)
    (Q : (n : ℕ) → Finpartition
      (Finset.univ : Finset (Fin (A.model (ν n)).size)))
    (C : (n : ℕ) → Finset (Fin (A.model (ν n)).size))
    (hC : ∀ n, C n ∈ (Q n).parts)
    (r : ℕ → ℕ) (hr : Tendsto r atTop atTop)
    (hmatched : Tendsto
      (fun n =>
        (((C n ∩ SoficGroups.matchedRadiusBad
          (Q n) (sourceProductRadiusLabels S F (r n))
          ((A.model (ν n)).action)
          (canonicalProductRadiusBad
            A S hsymmetric hgenerates F (ν n) (r n))).card : ℝ) /
            (C n).card))
      atTop (nhds 0))
    (D : (n : ℕ) → Finset
      {x : Fin (A.model (ν n)).size // x ∈ C n})
    (hZ : ∀ n,
      (Finset.univ \ D n :
        Finset {x : Fin (A.model (ν n)).size // x ∈ C n}).Nonempty)
    (hdeleted : Tendsto
      (fun n => ((D n).card : ℝ) / (C n).card)
      atTop (nhds 0))
    (a g : K) :
    Tendsto
      (fun n =>
        SoficGroups.normalizedHamming
          (completedRestriction
            (completedRestriction
              ((A.model (ν n)).action (a * g, (1 : J))) (C n))
            (Finset.univ \ D n))
          (completedRestriction
            (completedRestriction
              ((A.model (ν n)).action (a, (1 : J))) (C n))
            (Finset.univ \ D n) *
           completedRestriction
            (completedRestriction
              ((A.model (ν n)).action (g, (1 : J))) (C n))
            (Finset.univ \ D n)))
      atTop (nhds 0) := by sorry
