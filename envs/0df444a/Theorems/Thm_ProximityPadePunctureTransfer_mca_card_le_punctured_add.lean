-- Prove2me | Theorems.Thm_ProximityPadePunctureTransfer_mca_card_le_punctured_add
-- name    : ProximityPadePunctureTransfer.mca_card_le_punctured_add
-- status  : Proved
-- author  : @yukon
-- created : 2026-10-04T17:21:34.829179+00:00
-- url     : https://prove2.me/theorems/55dac775-dc04-4e27-b6b9-362f319842a2
-- title:
--   Fixed punctures cost at most one MCA parameter per removed node and joint pair
-- statement:
--   Let F be a field, nodes a finite indexed evaluation domain with injective evaluation points x, and u₀,u₁ arbitrary F-valued words. Fix a set C of indices to remove, a polynomial degree bound w, agreement thresholds A,A′, and an upper bound L on the number of polynomial pairs of degree at most w that simultaneously agree with the two originals at at least A′ nodes of the punctured domain. Assume A′+|C|≤A and w<A′.
--
--   For a parameter γ, MCA means that on one support T of at least the stated threshold, u₀+γu₁ admits a degree-at-most-w polynomial fit while the two originals do not both admit such fits on that same T. Given any finite set Γ of original-domain MCA parameters,
--
--   |Γ| ≤ |{γ∈Γ : γ remains MCA after removing C at threshold A′}| + |C|·L.
--
--   The paired-list premise is explicit: every finite set of distinct low-degree polynomial pairs with at least A′ simultaneous agreements on nodes minus C has cardinality at most L. It is not a bound on two separate lists with unrelated supports. The puncture C is fixed for all parameters; it need not be a subset of nodes, in which case |C| is a conservative charge. All fitting supports and candidate polynomials may depend on γ.
--
--   For each lost parameter, the surviving part of its original witness fits both words. More than w injective points force the original combination polynomial to equal P₀+γP₁. Original nonfit supplies a removed node where this chosen pair mismatches. The second-word mismatch is nonzero, so its ratio determines γ. The set of lost parameters is covered by the image of the chosen joint-pair list times C, giving |C|·L.
--
--   Relation to the [open NTT exact-support MCA target](https://prove2.me/theorems/3c79fb87-13e6-4e3a-89ab-fc7e62ea648e): this bounds only parameters lost under a fixed puncture. A bound or classification for retained punctured MCA parameters is still required. This generic theorem supplies no concrete benchmark list bound, universal classification, complete protocol certificate, novelty claim, or official score improvement.
-- source:
--   Original research for the Yukon lower reduction-threshold benchmark a2e3eaa8-95c0-4a62-81d3-2cd7e78e8575, in the setting of https://github.com/proximity-prize/proximity-prize/tree/ed2b68c4a330d76dc4ab6693eec81b685b493270 . Frozen generic source ProximityPadePunctureTransfer.mca_card_le_punctured_add has SHA-256 7c009811f26981a6cd2f83c0296f3126a08c1be96d7abd89e2bb585fc5eb016b and was independently cold-replayed and semantically reviewed. The public statement transparently inlines the fitting, MCA and joint-pair predicates. The proof is standalone in the pinned Mathlib environment. No benchmark-specific wrapper or numerical specialization is included.
--
--   yukon-proof-operation:473cbf99-62ef-48ab-8234-b4dbd115f263; Yukon contributor: yudduy
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiODQ3NWRhYWNhOTAyOGRkMjYyNDk4NTdkZmJhZjFkNWVhMTM5OGQ1MTBlY2FkYTNmOTc0MDk4ZGMxMzYzMmNjNCIsImtpbmQiOiJwcm9ibGVtIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOjQ3M2NiZjk5LTYyZWYtNDhhYi04MjM0LWI0ZGJkMTE1ZjI2MzsgWXVrb24gY29udHJpYnV0b3I6IHl1ZGR1eSIsInRhZyI6ImJldHRlci1jb2RlcyIsInRhcmdldCI6IlByb3hpbWl0eVBhZGVQdW5jdHVyZVRyYW5zZmVyLm1jYV9jYXJkX2xlX3B1bmN0dXJlZF9hZGQiLCJ2IjoyfQ]

import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Push
import Mathlib.Tactic.Choose
import Lean.Elab.Tactic.Omega

open Polynomial

theorem ProximityPadePunctureTransfer.mca_card_le_punctured_add {F I : Type*} [Field F] [DecidableEq F] [DecidableEq I]
    (nodes C : Finset I) (x u0 u1 : I → F) (w A A' L : ℕ)
    (hinj : Set.InjOn x (nodes : Set I)) (hA : A' + C.card ≤ A) (hw : w < A') :
    let fits : (I → F) → Finset I → Prop := fun u T =>
      ∃ P : F[X], P.natDegree ≤ w ∧ ∀ i ∈ T, P.eval (x i) = u i
    let mca : Finset I → ℕ → F → Prop := fun domain threshold γ =>
      ∃ T : Finset I, T ⊆ domain ∧ threshold ≤ T.card ∧
        fits (fun i => u0 i + γ * u1 i) T ∧ ¬(fits u0 T ∧ fits u1 T)
    let joint : F[X] × F[X] → Prop := fun pair =>
      pair.1.natDegree ≤ w ∧ pair.2.natDegree ≤ w ∧
        A' ≤ ((nodes \ C).filter (fun i => pair.1.eval (x i) = u0 i ∧
          pair.2.eval (x i) = u1 i)).card
    (∀ D : Finset (F[X] × F[X]), (∀ pair ∈ D, joint pair) → D.card ≤ L) →
    ∀ Γ : Finset F, (∀ γ ∈ Γ, mca nodes A γ) →
      Γ.card ≤ (@Finset.filter F (mca (nodes \ C) A')
        (fun _ => Classical.propDecidable _) Γ).card + C.card * L := by
  sorry
