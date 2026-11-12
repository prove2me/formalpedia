-- Prove2me | Theorems.Thm_QuantumScalingMWPM_QLiquidationist_lemma_8
-- name    : QuantumScalingMWPM.QLiquidationist.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:15:58.03275+00:00
-- url     : https://prove2.me/theorems/2af56a02-01fb-4ef0-8f7e-c6b7d299f770
-- title:
--   Lemma 8 — maximality of QUANTUMPATHSEARCH
-- statement:
--   Let $M$ be a matching of $G$, $\Omega$ a valid blossom family for $M$, $y$ vertex duals and $w$ integer weights. Conditioned on the correctness of every GROVERSEARCH call, when Algorithm 1 (QUANTUMPATHSEARCH) terminates with output $\Psi$, there is no eligible augmenting H-blossom path that is disjoint from every path of $\Psi$. Equivalently, every eligible augmenting path of blossoms in $H=G_{elig}/\Omega$ shares an H-blossom with some path of $\Psi$.
--
--   With Lemma 3, this shows that $\Psi$ is a maximal set of blossom-disjoint eligible augmenting paths, which is Task 1 of Figure 3.
--
--   Differences from the source:
--   - encoding: conditioned on the correctness of all calls to GROVERSEARCH → a nondeterministic transition system in which each GROVERSEARCH call returns some marked neighbour, and ⊥ exactly when none exists; the statement holds for every run; reason: this is the conditioning: every correct resolution of every call
--   - generalization: Algorithm 1 enumerates the free vertices (line 8) and the vertices of a blossom (foreach x ∈ V(B)) in an unspecified order → any order of the free vertices, and any enumeration order ord of each blossom (ValidOrd ord); reason: the source fixes no order; the statement for every order specializes to whatever order an implementation uses
--   - reading: the standing blossom invariant of §2.1 (p. 6: maintained "so that these facts always hold"; App. E, p. 39), not printed in the statement → hypotheses: M is a matching of G and Ω is a valid blossom family for M (IsBlossomFamily); reason: every call of the procedure in the source is made on such a structure; without it the objects of the statement (bases, blossom cycles) are undefined
-- source:
--   Kourosh Mirsohi, Sandy Irani, Michael Goodrich, STOC 2027 submission #842 (October 2026), Lemma 8, p. 18 (proof pp. 18–19); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/842.pdf

import Mathlib
import Definitions.Def_QuantumScalingMWPM_QLiquidationist_PathSearch

namespace QuantumScalingMWPM.QLiquidationist

variable {n : ℕ}

/-- Lemma 8 (Maximality of QUANTUMPATHSEARCH, p. 18). Conditioned on the correctness of all
GROVERSEARCH calls, when Algorithm 1 terminates every eligible augmenting H-blossom path shares
an H-blossom with some path of `Ψ`. -/
theorem lemma_8 (G : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → ℤ) (M : Mate n) (y : Fin n → ℤ)
    (Ω : Family n) (ord : Finset (Fin n) → List (Fin n))
    (hM : IsMatching G M) (hΩ : IsBlossomFamily G M Ω) (hord : ValidOrd ord)
    (s : Alg1State n) (hs : Alg1Final G w M y Ω ord s) :
    ∀ P, IsEligAugPathH G w M y Ω P → ∃ Q ∈ s.psi, ¬ BlossomDisjoint Ω P Q := by sorry

end QuantumScalingMWPM.QLiquidationist
