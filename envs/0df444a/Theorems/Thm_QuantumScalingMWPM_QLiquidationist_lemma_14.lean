-- Prove2me | Theorems.Thm_QuantumScalingMWPM_QLiquidationist_lemma_14
-- name    : QuantumScalingMWPM.QLiquidationist.lemma_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:16:05.725347+00:00
-- url     : https://prove2.me/theorems/c56eb30c-73a1-4406-b27d-727ec9b2462e
-- title:
--   Lemma 14 — exhaustion of Task 3
-- statement:
--   Let $M$ be a matching of $G$, $\Omega$ a valid blossom family for $M$, $y$ vertex duals and $w$ integer weights, and assume that there is no eligible augmenting path of blossoms in $G/\Omega$; this is the situation of Task 3 by Lemma 12. Consider any terminating run of Algorithm 1 on $(G,w,M,y,\Omega)$, all GROVERSEARCH calls correct. The current root blossoms are those of the final search-local family $\Omega'$. When the run terminates:
--   1. every OUT vertex is completely scanned, that is, some GROVERSEARCH call from it returned $\bot$;
--   2. no Criterion-2 eligible edge joins an OUT vertex to an UNLABELED vertex in a distinct current root blossom;
--   3. no Criterion-2 eligible edge joins two OUT vertices whose endpoints lie in distinct current root blossoms.
--
--   These are the termination conditions that make Task 3 the blossom-detection task of classical SEARCHONE: every eligible OUT–OUT edge has been absorbed into a blossom.
--
--   Differences from the source:
--   - encoding: conditioned on the correctness of all calls to GROVERSEARCH → a nondeterministic transition system in which each GROVERSEARCH call returns some marked neighbour, and ⊥ exactly when none exists; the statement holds for every run; reason: this is the conditioning: every correct resolution of every call
--   - generalization: Algorithm 1 enumerates the free vertices (line 8) and the vertices of a blossom (foreach x ∈ V(B)) in an unspecified order → any order of the free vertices, and any enumeration order ord of each blossom (ValidOrd ord); reason: the source fixes no order; the statement for every order specializes to whatever order an implementation uses
--   - reading: the standing blossom invariant of §2.1 (p. 6: maintained "so that these facts always hold"; App. E, p. 39), not printed in the statement → hypotheses: M is a matching of G and Ω is a valid blossom family for M (IsBlossomFamily); reason: every call of the procedure in the source is made on such a structure; without it the objects of the statement (bases, blossom cycles) are undefined
--   - generalization: when Task 3 (run after Task 2) terminates → every terminating run of Algorithm 1 on any valid input without an eligible augmenting path in G/Ω; reason: the input of Task 3 is such an input by Lemma 12 (and Fact 1 for the validity of the re-based family), so the statement specializes to Task 3
-- source:
--   Kourosh Mirsohi, Sandy Irani, Michael Goodrich, STOC 2027 submission #842 (October 2026), Lemma 14, p. 21 (proof pp. 21–22); §3.4, p. 21; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/842.pdf

import Mathlib
import Definitions.Def_QuantumScalingMWPM_QLiquidationist_PathSearch

namespace QuantumScalingMWPM.QLiquidationist

variable {n : ℕ}

/-- Lemma 14 (Exhaustion of Task 3, p. 21). Run Algorithm 1 on a matching and blossom family
with no eligible augmenting path in `G/Ω` (the situation of Task 3). When it terminates:
1. every OUT vertex is completely scanned;
2. no eligible edge joins an OUT vertex to an UNLABELED vertex in a distinct current root
   blossom;
3. no eligible edge joins two OUT vertices in distinct current root blossoms. -/
theorem lemma_14 (G : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → ℤ) (M : Mate n) (y : Fin n → ℤ)
    (Ω : Family n) (ord : Finset (Fin n) → List (Fin n))
    (hM : IsMatching G M) (hΩ : IsBlossomFamily G M Ω) (hord : ValidOrd ord)
    (hno : ∀ P, ¬ IsEligAugPathH G w M y Ω P)
    (s : Alg1State n) (hs : Alg1Final G w M y Ω ord s) :
    (∀ v, s.uio v = .out → v ∈ s.scanned) ∧
      (∀ v u, s.uio v = .out → s.uio u = .unl → rootSet s.fam v ≠ rootSet s.fam u →
        ¬ Elig2 G w M y v u) ∧
      (∀ v u, s.uio v = .out → s.uio u = .out → rootSet s.fam v ≠ rootSet s.fam u →
        ¬ Elig2 G w M y v u) := by sorry

end QuantumScalingMWPM.QLiquidationist
