-- Prove2me | Theorems.Thm_ReplicableDecisions_lemma_2_2
-- name    : ReplicableDecisions.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:07:36.836192+00:00
-- url     : https://prove2.me/theorems/b1d75f75-469e-4bdf-b5da-bbc15c495bfb
-- title:
--   Lemma 2.2 — graph form: $D_r\le L\iff s_L\le r$, and the strict version
-- statement:
--   Suppose $A_0,A_1\ne\emptyset$. For $r>0$ and an integer $L\ge1$,
--
--   $$
--   D_r\le L\iff s_L\le r,\qquad \mathrm{dist}_{G_{<r}}(A_0,A_1)\le L\iff s_L<r .
--   $$
--
--   The lemma translates between the hop count of a Hellinger graph and the bottleneck scale of chains.
--
--   Differences from the source:
--   - encoding: a known family P = {P1, …, PM} of distinct distributions on a finite set Z → an `Experiment ι Z`: an injective table of probability vectors over a finite index type, with Z in `Type` and M = `Fintype.card ι`; reason: models are named by index; the reused Bhattacharyya coefficient takes a type in `Type`, which loses no finite Z
--   - encoding: Y = {0, 1} → `Bool`, with 0 = `false` and 1 = `true`; reason: same two outputs
--   - encoding: s_L as a minimum over chains Q0, …, Qℓ → `sInf` of the finite nonempty value set, chains as `Fin (ℓ + 1) → ι`; reason: under A0, A1 ≠ ∅ and L ≥ 1 the set is finite and nonempty, and a proved sanity check shows that the infimum is attained
-- source:
--   Chen, Replicable Decisions in Finite Experiments, STOC 2027 submission (sha256 52d181db…), Lemma 2.2, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_ReplicableDecisions_hopSeparation
import Definitions.Def_ReplicableDecisions_weakGraph

namespace ReplicableDecisions

/-- **Lemma 2.2 (Graph form).** Chen, *Replicable Decisions in Finite Experiments*, STOC 2027 submission
(sha256 52d181db…), Lemma 2.2, p.10 (PDF p.12): "For r > 0 and an integer L ≥ 1, D_r ≤ L if and only if
s_L ≤ r. Likewise, dist_{G_{<r}}(A0, A1) ≤ L if and only if s_L < r."

**Formalization Note.** `A₀, A₁ ≠ ∅` is the standing assumption of Definition 2.1. -/
theorem lemma_2_2 {ι : Type*} {Z : Type} [Fintype ι] [Fintype Z] (E : Experiment ι Z)
    (Γ : ι → Set Bool) (hΓ : ∀ i, (Γ i).Nonempty) (hA₀ : (forcedClass Γ false).Nonempty)
    (hA₁ : (forcedClass Γ true).Nonempty) {r : ℝ} (hr : 0 < r) {L : ℕ} (hL : 1 ≤ L) :
    (forcedDist (weakGraph E r) Γ false true ≤ L ↔ hopSeparation E Γ L ≤ r) ∧
      (forcedDist (strictGraph E r) Γ false true ≤ L ↔ hopSeparation E Γ L < r) := by sorry

end ReplicableDecisions
