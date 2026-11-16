-- Prove2me | Theorems.Thm_PolyTimeMBLG_Monotone_Supplement_lemma_13
-- name    : PolyTimeMBLG.Monotone.Supplement.lemma_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:33:51.48612+00:00
-- url     : https://prove2.me/theorems/01f987fe-740a-4d79-8e7e-8a8237fc4f01
-- title:
--   Lemma 13 — if disjunctions of 3 literals are polynomial-time MBLG, so are 3-CNFs
-- statement:
--   Let $\{F_n\}$ be the family of disjunctions of 3 literals $x_{i_1}^{\alpha_1}\vee x_{i_2}^{\alpha_2}\vee x_{i_3}^{\alpha_3}$ on pairwise distinct variables among $x_1,\dots,x_n$, and $\{F'_n\}$ the family of 3-CNFs $D_1\wedge\cdots\wedge D_m$ ($m\ge0$) of clauses of at most 3 literals (for $n\ge3$, exactly the conjunctions of members of $F_n$). If $\{F_n\}$ is polynomial-time MBLG, then $\{F'_n\}$ is polynomial-time MBLG:
--   $$\{F_n\}\ \text{polynomial-time MBLG}\quad\Longrightarrow\quad\{F'_n\}\ \text{polynomial-time MBLG}.$$
--
--   Here polynomial-time MBLG is Definition 6: $|F_n|\le 2^{q(n)}$ for a polynomial $q$ and all $n\ge1$, and one generator, computed by one Turing machine in time polynomial in the length of its input $(1^n,x^1\cdots x^i)$, makes at most $e(n)$ mistakes for a polynomial $e$ on every $L\in F_n$, every enumeration of $L$ and every $n\ge1$.
--
--   This is the first step of the proof of Theorem 3: generation for single clauses extends to arbitrary conjunctions of them.
--
--   **Formalization Note** Polynomial-time MBLG is the base mission's published `IsPolyTimeMBLG`.
--
--   Differences from the source:
--   - reading: "disjunction of 3 literals" → three literals on pairwise distinct variables; reason: the stronger of the two readings (the hypothesis is about a smaller family; the family with repeated indices contains it); the paper writes literal combinations with distinct indices (Proposition 7, p. 6).
--   - reading: "3-CNF" → a conjunction of any finite number $m\ge0$ of clauses of at most 3 literals (indices may repeat), with no cap on $m$; reason: the usual meaning, and the clauses the Circuit-SAT to 3-SAT reduction of Lemma 14 produces; for $n\ge3$ these are exactly the conjunctions of disjunctions of 3 literals on distinct variables, and the bound $m\le O(n^3)$ on p. 9 holds after removing repeated clauses.
--   - encoding: polynomial-time MBLG (Definition 6) → the base mission's `IsPolyTimeMBLG` (TM2 machine, encoding of length $(n+1)(i+1)$, polynomials with natural coefficients); reason: the published definition of the mission, whose equivalence with the paper's notion is recorded there.
-- source:
--   Héctor Jimenez, Alexander Kozachinskiy, Vicente Opazo, STOC 2027 submission #402 (October 2026), Lemma 13 and its proof, p. 9; Definition 6, p. 5. PDF SHA-256 2e6ec485290626cb762f55f7c45588eeb0047572a27748b20af18d34ebad7511, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/402.pdf

import Mathlib
import Definitions.Def_PolyTimeMBLG_Monotone_Generation
import Definitions.Def_PolyTimeMBLG_Monotone_Supplement_Clauses

namespace PolyTimeMBLG.Monotone.Supplement

/-- Lemma 13, p. 9: if the family of disjunctions of 3 literals is polynomial-time MBLG, then the
family of 3-CNFs is polynomial-time MBLG (Definition 6, p. 5). -/
theorem lemma_13 (h : IsPolyTimeMBLG disj3Family) : IsPolyTimeMBLG cnf3Family := by sorry

end PolyTimeMBLG.Monotone.Supplement
