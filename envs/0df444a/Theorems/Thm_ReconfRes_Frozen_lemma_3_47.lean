-- Prove2me | Theorems.Thm_ReconfRes_Frozen_lemma_3_47
-- name    : ReconfRes.Frozen.lemma_3_47
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:23:22.787457+00:00
-- url     : https://prove2.me/theorems/d9c895ee-314b-4bc6-a368-78dc41d6e3c3
-- title:
--   Lemma 3.47 — at budget 2α − 1 every lean refutation is a read-once tree; frozen moves keep t resolution nodes and the same t + 1 inputs, and reverse
-- statement:
--   Fix a multiset $M$ of $\alpha\ge1$ axiom clauses and the size budget $s=2\alpha-1$. Every lean refutation with axiom multiset $M$ and size at most $s$ is a read-once resolution tree without weakening nodes. If a frozen move (of any locality $k\ge1$) replaces a block $Q$ of $t$ inference nodes by $Q'$ between two such refutations, then both blocks have exactly $t$ resolution nodes and exactly the same $t+1$ distinct input nodes, each used once, and the reverse replacement is also a frozen move:
--   $$|Q'|=|Q|=t,\qquad \mathrm{in}(Q')=\varphi(\mathrm{in}(Q)),\qquad |\mathrm{in}(Q)|=t+1 .$$
--   This tight-boundary lemma is what makes frozen moves at the minimum budget reversible and decodable.
--
--   Differences from the source:
--   - encoding: a frozen move replacing a block of t inference nodes between two such refutations → a move given by its data (Q, Q′, φ) between refutations of a common formula F; t = |Q|; "the same inputs" = φ carries the inputs of Q onto those of Q′; reason: moves are defined relative to F and to the identification of the kept nodes (Definition 3.2)
-- source:
--   Myrisiotis, Reconfiguring Resolution Refutations, STOC 2027 submission (manuscript sha256 8b5124c1…), pp. 58–59, Lemma 3.47

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_CNF
import Definitions.Def_ReconfRes_Frozen_Refutation
import Definitions.Def_ReconfRes_Frozen_FrozenGraph

open MultiplierAssoc206.Resolution

namespace ReconfRes.Frozen

/-- **Lemma 3.47** (frozen moves at the minimum budget). Fix a multiset `M` of `α ≥ 1` axiom
clauses and the size budget `2α − 1`. Every lean refutation with axiom multiset `M` and size at
most `2α − 1` is a read-once resolution tree without weakening. If a frozen move replaces a block
`Q` of `t` inference nodes by `Q'` between two such refutations, then both blocks consist of
exactly `t` resolution nodes, they have exactly the same `t + 1` distinct input nodes (`φ` maps
the inputs of `Q` onto those of `Q'`), each used once, and the reverse replacement is also a
frozen move. -/
theorem lemma_3_47 {V : Type} [DecidableEq V] (F : CNF V) (M : Multiset (Clause V))
    (hM : 1 ≤ Multiset.card M) :
    (∀ R : ProofDag V, R.IsRefutationOf F → R.IsLean → R.axiomMultiset = M →
      R.size + 1 ≤ 2 * Multiset.card M → R.IsReadOnce) ∧
    (∀ (k : ℕ) (R R' : ProofDag V) (Q : Finset (Fin R.n)) (Q' : Finset (Fin R'.n))
      (φ : {i // i ∉ Q} ≃ {j // j ∉ Q'}), 1 ≤ k →
      R.IsRefutationOf F → R.IsLean → R.axiomMultiset = M → R.size + 1 ≤ 2 * Multiset.card M →
      R'.IsRefutationOf F → R'.IsLean → R'.axiomMultiset = M →
      R'.size + 1 ≤ 2 * Multiset.card M →
      FrozenMoveVia k R R' Q Q' φ →
      Q'.card = Q.card ∧
      (∀ i ∈ Q, R.IsResolutionNode i) ∧ (∀ j ∈ Q', R'.IsResolutionNode j) ∧
      (R.inputs Q).card = Q.card + 1 ∧
      (∀ i : {i // i ∉ Q}, i.1 ∈ R.inputs Q ↔ (φ i).1 ∈ R'.inputs Q') ∧
      (∀ i ∈ R.inputs Q, ((R.consumers i).filter (· ∈ Q)).card = 1) ∧
      (∀ j ∈ R'.inputs Q', ((R'.consumers j).filter (· ∈ Q')).card = 1) ∧
      FrozenMoveVia k R' R Q' Q φ.symm) := by sorry

end ReconfRes.Frozen
