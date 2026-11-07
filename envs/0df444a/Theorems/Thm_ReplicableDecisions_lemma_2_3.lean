-- Prove2me | Theorems.Thm_ReplicableDecisions_lemma_2_3
-- name    : ReplicableDecisions.lemma_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:08:20.258081+00:00
-- url     : https://prove2.me/theorems/7b4865fd-0acf-4e6e-b41d-f57f757047ce
-- title:
--   Lemma 2.3 — hop refinement: $s_{aL}\ge s_L/a$
-- statement:
--   Suppose $A_0,A_1\ne\emptyset$. For all integers $a,L\ge1$,
--
--   $$
--   s_{aL}\ge\frac{s_L}{a}.
--   $$
--
--   This is the one geometric input that reconciles the two hop budgets of the goal theorem, and the source of the factor $12^2$ in $4608$.
--
--   Differences from the source:
--   - encoding: a known family P = {P1, …, PM} of distinct distributions on a finite set Z → an `Experiment ι Z`: an injective table of probability vectors over a finite index type, with Z in `Type` and M = `Fintype.card ι`; reason: models are named by index; the reused Bhattacharyya coefficient takes a type in `Type`, which loses no finite Z
--   - encoding: Y = {0, 1} → `Bool`, with 0 = `false` and 1 = `true`; reason: same two outputs
--   - encoding: s_L as a minimum over chains Q0, …, Qℓ → `sInf` of the finite nonempty value set, chains as `Fin (ℓ + 1) → ι`; reason: under A0, A1 ≠ ∅ and L ≥ 1 the set is finite and nonempty, and a proved sanity check shows that the infimum is attained
-- source:
--   Chen, Replicable Decisions in Finite Experiments, STOC 2027 submission (sha256 52d181db…), Lemma 2.3, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_ReplicableDecisions_hopSeparation

namespace ReplicableDecisions

/-- **Lemma 2.3 (Hop refinement).** Chen, *Replicable Decisions in Finite Experiments*, STOC 2027
submission (sha256 52d181db…), Lemma 2.3, p.10 (PDF p.12): "For all integers a, L ≥ 1, s_{aL} ≥ s_L/a."

**Formalization Note.** `A₀, A₁ ≠ ∅` is the standing assumption of Definition 2.1. -/
theorem lemma_2_3 {ι : Type*} {Z : Type} [Fintype ι] [Fintype Z] (E : Experiment ι Z)
    (Γ : ι → Set Bool) (hΓ : ∀ i, (Γ i).Nonempty) (hA₀ : (forcedClass Γ false).Nonempty)
    (hA₁ : (forcedClass Γ true).Nonempty) {a L : ℕ} (ha : 1 ≤ a) (hL : 1 ≤ L) :
    hopSeparation E Γ L / a ≤ hopSeparation E Γ (a * L) := by sorry

end ReplicableDecisions
