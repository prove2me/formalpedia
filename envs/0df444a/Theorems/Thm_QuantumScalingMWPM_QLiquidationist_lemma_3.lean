-- Prove2me | Theorems.Thm_QuantumScalingMWPM_QLiquidationist_lemma_3
-- name    : QuantumScalingMWPM.QLiquidationist.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:15:45.016471+00:00
-- url     : https://prove2.me/theorems/12ed4438-bbd9-43ec-aa31-fd229b6c34cb
-- title:
--   Lemma 3 — the paths returned by QUANTUMPATHSEARCH are eligible, H-blossom-disjoint and liftable
-- statement:
--   Let $M$ be a matching of $G$ and $\Omega$ a valid blossom family for $M$. The H-blossoms are the root blossoms of $\Omega$, the vertices of $H=G_{elig}/\Omega$. Let $y$ be vertex duals and $w$ integer weights. Conditioned on the correctness of every GROVERSEARCH call, consider any terminating run of Algorithm 1 (QUANTUMPATHSEARCH) on $(G,w,M,y,\Omega)$ and its output $\Psi$. Then:
--   1. every $P\in\Psi$ is an eligible augmenting path of H-blossoms (Definition 1 with every edge satisfying Criterion 2);
--   2. the paths of $\Psi$ are pairwise H-blossom-disjoint, that is, no H-blossom lies on two of them;
--   3. every $P\in\Psi$ lifts to $G$: its expansion along the stored defining cycles (Lemma 26, Fact 1) is an augmenting path of $G$ whose vertices lie in the H-blossoms of $P$.
--
--   Lemma 3, with Lemma 8, shows that Task 1 of QSEARCHONE finds a set of blossom-disjoint eligible augmenting paths that Task 2 can augment along.
--
--   Differences from the source:
--   - encoding: conditioned on the correctness of all calls to GROVERSEARCH → a nondeterministic transition system in which each GROVERSEARCH call returns some marked neighbour, and ⊥ exactly when none exists; the statement holds for every run; reason: this is the conditioning: every correct resolution of every call
--   - generalization: Algorithm 1 enumerates the free vertices (line 8) and the vertices of a blossom (foreach x ∈ V(B)) in an unspecified order → any order of the free vertices, and any enumeration order ord of each blossom (ValidOrd ord); reason: the source fixes no order; the statement for every order specializes to whatever order an implementation uses
--   - reading: the standing blossom invariant of §2.1 (p. 6: maintained "so that these facts always hold"; App. E, p. 39), not printed in the statement → hypotheses: M is a matching of G and Ω is a valid blossom family for M (IsBlossomFamily); reason: every call of the procedure in the source is made on such a structure; without it the objects of the statement (bases, blossom cycles) are undefined
--   - reading: each path can be lifted to the original graph G in time linear in its expanded length → the lift is the canonical expansion liftG (Lemma 26, Fact 1), stated to be an augmenting path of G inside the path's blossoms; its time is the mission's accounting of Fact 1 (task2Cost charges a lift its length), not a separate conjunct; reason: the source gives no lifting procedure beyond Lemma 26 and Fact 1, whose linear-time claim is the accounting convention; the conjunct states the substantive part, that the expansion is a valid augmenting path
-- source:
--   Kourosh Mirsohi, Sandy Irani, Michael Goodrich, STOC 2027 submission #842 (October 2026), Lemma 3, p. 13 (proof pp. 13, 16); Algorithm 1, p. 14; Fact 1, p. 6; Lemma 26, p. 39; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/842.pdf

import Mathlib
import Definitions.Def_QuantumScalingMWPM_QLiquidationist_PathSearch

namespace QuantumScalingMWPM.QLiquidationist

variable {n : ℕ}

/-- Lemma 3 (p. 13). Conditioned on the correctness of all GROVERSEARCH calls, every path that
Algorithm 1 adds to `Ψ` is an eligible augmenting path of H-blossoms (root blossoms of `Ω`) whose
lift to `G` is an augmenting path of `G` inside its blossoms, and the paths of `Ψ` are pairwise
H-blossom-disjoint. -/
theorem lemma_3 (G : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → ℤ) (M : Mate n) (y : Fin n → ℤ)
    (Ω : Family n) (ord : Finset (Fin n) → List (Fin n))
    (hM : IsMatching G M) (hΩ : IsBlossomFamily G M Ω) (hord : ValidOrd ord)
    (s : Alg1State n) (hs : Alg1Final G w M y Ω ord s) :
    (∀ P ∈ s.psi, IsEligAugPathH G w M y Ω P ∧ IsAugPathG G M (liftG Ω P) ∧
        ∀ e ∈ liftG Ω P, rootSet Ω e.1 ∈ blossomsOf Ω P ∧ rootSet Ω e.2 ∈ blossomsOf Ω P) ∧
      s.psi.Pairwise (BlossomDisjoint Ω) := by sorry

end QuantumScalingMWPM.QLiquidationist
