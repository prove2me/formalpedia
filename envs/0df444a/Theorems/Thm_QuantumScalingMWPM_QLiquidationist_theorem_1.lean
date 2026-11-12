-- Prove2me | Theorems.Thm_QuantumScalingMWPM_QLiquidationist_theorem_1
-- name    : QuantumScalingMWPM.QLiquidationist.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:16:02.095662+00:00
-- url     : https://prove2.me/theorems/af241b45-63f8-487c-aa2b-56a49499708a
-- title:
--   Theorem 1 — QSEARCHONE performs the tasks of SEARCHONE (Figure 3)
-- statement:
--   Let $M$ be a matching of $G$, $\Omega$ a valid blossom family for $M$, $y$ and $z$ dual variables and $w$ integer weights. Conditioned on the correctness of every GROVERSEARCH call, every run of QSEARCHONE on $(M,\Omega,y,z)$ produces a matching $M'$, a blossom family $\Omega'$ and duals $y'$, $z'$ that meet the specification of the five tasks of classical SEARCHONE in Figure 3 (with the dual adjustment of §3.5). That is, there are $\Psi$ and new blossoms such that:
--   1. $\Psi$ is a maximal set of blossom-disjoint eligible augmenting paths in $G/\Omega$;
--   2. $M'$ is $M$ augmented along their lifts;
--   3. the new blossoms are eligible odd alternating cycles with an OUT base, contracted until no eligible OUT–OUT edge joins distinct root blossoms, and they get $z=0$;
--   4. $y'$ and $z'$ are the dual adjustment on the even/odd alternating reachability sets $V_{OUT}$, $V_{IN}$ of the new contracted graph;
--   5. $\Omega'$ arises by dissolving the root blossoms with $z'=0$.
--
--   So QSEARCHONE can replace SEARCHONE inside FREEVERTEXREDUCTION, which is what Theorem 3 needs.
--
--   Differences from the source:
--   - encoding: conditioned on the correctness of all calls to GROVERSEARCH → a nondeterministic transition system in which each GROVERSEARCH call returns some marked neighbour, and ⊥ exactly when none exists; the statement holds for every run; reason: this is the conditioning: every correct resolution of every call
--   - generalization: Algorithm 1 enumerates the free vertices (line 8) and the vertices of a blossom (foreach x ∈ V(B)) in an unspecified order → any order of the free vertices, and any enumeration order ord of each blossom (ValidOrd ord); reason: the source fixes no order; the statement for every order specializes to whatever order an implementation uses
--   - reading: the standing blossom invariant of §2.1 (p. 6: maintained "so that these facts always hold"; App. E, p. 39), not printed in the statement → hypotheses: M is a matching of G and Ω is a valid blossom family for M (IsBlossomFamily); reason: every call of the procedure in the source is made on such a structure; without it the objects of the statement (bases, blossom cycles) are undefined
--   - reading: QSEARCHONE correctly performs all of the tasks as the classical SEARCHONE as outlined in Figure 3 → every run of QSearchOne satisfies SearchOneSpec, the relational form of the five tasks of Figure 3 with the dual adjustment of §3.5; reason: Figure 3 describes tasks, not a program, and SEARCHONE is itself nondeterministic; "performs the same tasks" is satisfying their specification
--   - reading: Task 3: build a search forest, repeatedly contract the odd cycle closed by an OUT–OUT edge in one tree, until no eligible OUT–OUT edges remain → a sequence of contractions, each an eligible odd alternating cycle of current root blossoms with OUT base child, ending with a valid blossom family in which no eligible edge joins two V_OUT vertices of distinct root blossoms; reason: this is the postcondition of the described contraction loop; OUT and IN are the even/odd reachability of §3.5
--   - reading: Task 2: the matching is updated, but the blossom structure remains unchanged → the blossom sets and defining cycles are unchanged; each stored cycle is rotated so that its new base child comes first (rebase); reason: proof of Fact 1, p. 40: augmentation only changes which child acts as the base child
--   - reading: Task 5: for any root blossom B such that z(B) = 0, dissolve B → one pass: the root blossoms of the family after Task 4 with z = 0 are removed; reason: the printed task names the root blossoms present when it runs
-- source:
--   Kourosh Mirsohi, Sandy Irani, Michael Goodrich, STOC 2027 submission #842 (October 2026), Theorem 1, p. 23 (proof p. 23); Figure 3, p. 7; §3.5, p. 22; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/842.pdf

import Mathlib
import Definitions.Def_QuantumScalingMWPM_QLiquidationist_PathSearch

namespace QuantumScalingMWPM.QLiquidationist

variable {n : ℕ}

/-- Theorem 1 (p. 23). QSEARCHONE correctly performs the tasks of the classical SEARCHONE
(Figure 3): every run of QSEARCHONE (with correct searches) produces a matching, blossom family
and duals that satisfy the Figure 3 specification. -/
theorem theorem_1 (G : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → ℤ)
    (ord : Finset (Fin n) → List (Fin n)) (M : Mate n) (Ω : Family n) (y : Fin n → ℤ)
    (z : Finset (Fin n) → ℤ)
    (hM : IsMatching G M) (hΩ : IsBlossomFamily G M Ω) (hord : ValidOrd ord)
    (r : QSOneResult n) (hr : QSearchOne G w ord M Ω y z r) :
    SearchOneSpec G w M Ω y z r.M r.fam r.y r.z := by sorry

end QuantumScalingMWPM.QLiquidationist
