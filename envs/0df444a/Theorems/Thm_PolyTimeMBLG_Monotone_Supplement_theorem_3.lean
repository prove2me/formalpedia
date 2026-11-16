-- Prove2me | Theorems.Thm_PolyTimeMBLG_Monotone_Supplement_theorem_3
-- name    : PolyTimeMBLG.Monotone.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:36:06.251887+00:00
-- url     : https://prove2.me/theorems/7d76d0b5-bf44-4987-bd09-6813a676b21e
-- title:
--   Theorem 3 — if one-way functions exist, disjunctions of 3 literals are not polynomial-time MBLG
-- statement:
--   Assume that a one-way function exists: a polynomial-time computable $f:\{0,1\}^*\to\{0,1\}^*$ such that no polynomial-time randomized algorithm, given $1^n$ and $f(x)$ for uniform $x\in\{0,1\}^n$, returns some $\hat x\in\{0,1\}^n$ with $f(\hat x)=f(x)$ with probability at least $1/\mathrm{poly}(n)$ for infinitely many $n$ (Definition 21). Then the family $\{F_n\}_{n\ge1}$ of disjunctions of 3 literals,
--   $$F_n=\bigl\{\{x\in\{0,1\}^n : x\models x_{i_1}^{\alpha_1}\vee x_{i_2}^{\alpha_2}\vee x_{i_3}^{\alpha_3}\}\ :\ i_1,i_2,i_3\in\{1,\dots,n\}\ \text{pairwise distinct},\ \alpha_j\in\{0,1\}\bigr\},$$
--   is **not** polynomial-time MBLG: no generator computed by a Turing machine in polynomial time makes only polynomially many mistakes on it.
--
--   The family has only $O(n^3)$ members, so a generator unconstrained in time makes $O(\log n)$ mistakes on it (Kleinberg, Peale and Reingold); the theorem says that, under the cryptographic assumption, no polynomial-time generator makes even $\mathrm{poly}(n)$ mistakes. It contrasts with the mission's goal, Theorem 11: monotone disjunctions (one maxterm) are polynomial-time MBLG unconditionally.
--
--   **Formalization Note** One-way functions are Definition 21 as formalized in this mission, and polynomial-time MBLG is the base mission's published `IsPolyTimeMBLG`; the negation covers every polynomial-time generator and every polynomial mistake bound.
--
--   Differences from the source:
--   - reading: "disjunction of 3 literals" → three literals on pairwise distinct variables; reason: the stronger of the two readings: this family is contained in the one allowing repeated indices and polynomial-time MBLG passes to subfamilies, so the statement implies the repeated-index version; the paper writes literal combinations with distinct indices (Proposition 7, p. 6).
--   - encoding: polynomial-time MBLG (Definition 6) → the base mission's `IsPolyTimeMBLG` (TM2 machine, encoding of length $(n+1)(i+1)$, polynomials with natural coefficients); reason: the published definition of the mission.
--   - encoding: polynomial-time randomized inverter → a polynomial-time TM2 machine on $(1^n,f(x))$ and a coin string of length $c(n)$ for a polynomial $c$, with success probability the exact fraction of pairs $(x,r)$; reason: the length of $f(x)$ is polynomial in $n$, so polynomially many coins and polynomial time in the input length are the standard notions.
--   - encoding: "with probability $1/\mathrm{poly}(n)$" → $1\le q(n)\cdot\Pr[\text{success}]$ for a polynomial $q$ with natural coefficients; reason: every positive inverse-polynomial lower bound is of this form.
-- source:
--   Héctor Jimenez, Alexander Kozachinskiy, Vicente Opazo, STOC 2027 submission #402 (October 2026), Theorem 3, p. 4; proof §6 (Lemmas 13–15), pp. 9–10; Definition 21, p. 13; Definition 6, p. 5. PDF SHA-256 2e6ec485290626cb762f55f7c45588eeb0047572a27748b20af18d34ebad7511, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/402.pdf

import Mathlib
import Definitions.Def_PolyTimeMBLG_Monotone_Generation
import Definitions.Def_PolyTimeMBLG_Monotone_Supplement_Clauses
import Definitions.Def_PolyTimeMBLG_Monotone_Supplement_OneWay

namespace PolyTimeMBLG.Monotone.Supplement

/-- Theorem 3, p. 4 (proof §6, pp. 9–10): assuming the existence of a one-way function
(Definition 21, p. 13), the family of disjunctions of 3 literals is not polynomial-time MBLG
(Definition 6, p. 5). -/
theorem theorem_3 (hOWF : ∃ f : List Bool → List Bool, IsOneWay f) :
    ¬ IsPolyTimeMBLG disj3Family := by sorry

end PolyTimeMBLG.Monotone.Supplement
