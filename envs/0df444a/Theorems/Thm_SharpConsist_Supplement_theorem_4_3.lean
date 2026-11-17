-- Prove2me | Theorems.Thm_SharpConsist_Supplement_theorem_4_3
-- name    : SharpConsist.Supplement.theorem_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:23:50.337789+00:00
-- url     : https://prove2.me/theorems/a524b6fd-5d1f-4d51-8836-58c846578579
-- title:
--   Theorem 4.3 — a $(2-\sqrt2)$-robust core with $O(|X|\kappa)$ queries in polynomial time
-- statement:
--   Fix a current set $X$, an integer capacity $\kappa\ge1$ and a normalized monotone submodular objective $f$ on $2^X$, accessed only through value queries $f(S)$, $S\subseteq X$. A **legal future** is a monotone submodular $h:2^X\to\mathbb R_{\ge0}$ with $h\ge f$ and $0\le h(S\cup\{i\})-h(S)\le f(i\mid S)$ (Definition 2.1).
--
--   There are an absolute constant $C>0$ and one randomized algorithm (a program of the counted real-RAM oracle machine) with a polynomial running-time bound $c\,(|X|+\kappa+1)^d$ such that, for every $X$, $\kappa\ge1$ and $f$:
--
--   1. on every outcome, it halts within $c\,(|X|+\kappa+1)^d$ steps, makes at most $C\,|X|\,\kappa$ value queries, and outputs $A\subseteq X$ with $|A|\le\kappa$;
--   2. $A$ is a random variable whose law does not depend on $h$, and for every fixed legal future $h$,
--   $$\mathbb E\,h(A)\ \ge\ (2-\sqrt2)\max_{O\subseteq X,\ |O|\le\kappa} h(O).$$
--
--   This is the static subroutine behind Theorem 1.1(i): the checkpoint conversion (Lemma 2.3) turns it into the online algorithm.
--
--   Differences from the source:
--   - reading: for every current set X and capacity κ ≥ 1 there is a randomized algorithm … making O(|X|κ) queries and running in polynomial time → one program P, one absolute C and one polynomial c(n+κ+1)^d for all n = |X| and κ; reason: per-(X, κ) algorithms would make the cost claims vacuous; the uniform version implies the per-(X, κ) one
--   - reading: a randomized value-oracle algorithm with unit-cost queries, exact arithmetic and exact sampling (§2.1, p.4), performing polynomially many arithmetic operations → a program of OracleRAM: the published SmaleNinth real pointer RAM (exact + − × ÷, comparisons, pointers, no floor) with a Uniform[0,1] tape, a value-query instruction on a set marked in memory, and a halt-with-output instruction; rational literals; every executed instruction costs one step and the per-call step count is bounded by c(·+·+1)^d; reason: the page fixes the cost model only in words; this is the standard real RAM of that description; rational literals and the step bound on every tape only restrict the algorithm
--   - encoding: current set X; f the normalized monotone submodular objective on 2^X → X = Fin n, f with PolyContract.IsRankFunction f, read on index sets by natFn; reason: a finite set is in bijection with Fin n; the algorithm sees only values
--   - encoding: bounds on every outcome of the randomness; algorithms terminate almost surely (§2.1) → query bound, |A| ≤ κ and termination within the step budget required for every tape; reason: worst case over outcomes as on the page; requiring it on null sets too only restricts the algorithm
--   - encoding: E h(A), an expectation over the algorithm's randomness → the conclusion also asserts that {ω | A(ω) = S} is measurable for every S, and the expectation is the integral over the tape law; reason: makes the expectation genuine; it only adds to what the algorithm must satisfy
-- source:
--   Fu–Zhang–Tao, A Sharp Barrier of Consistent Submodular Maximization, arXiv:2609.09986 (held version, sha256 874ec76c…), §4.2, Theorem 4.3, p.11; Definitions 2.1–2.2, pp.4–5; §2.1, p.4

import Mathlib
import Definitions.Def_PolyContract_IsRankFunction
import Definitions.Def_SharpConsist_OPTk
import Definitions.Def_SharpConsist_Supplement_natFn
import Definitions.Def_SharpConsist_Supplement_IsLegalFuture
import Definitions.Def_SharpConsist_Supplement_OracleRAM

namespace SharpConsist.Supplement

open SharpConsist.Supplement.OracleRAM

/-- **Theorem 4.3 (a `(2 − √2)`-robust core).** Fu–Zhang–Tao, *A Sharp Barrier of Consistent
Submodular Maximization*, arXiv:2609.09986 (held version, sha256 874ec76c…), §4.2, Theorem 4.3,
p.11; Definitions 2.1–2.2, pp.4–5; computation model §2.1, p.4.

There are an absolute constant `C > 0`, one program `P` of the counted real-RAM oracle machine
(rational literals) and a polynomial bound `c (n + κ + 1)^d` such that, for every current set
`X = Fin n`, every integer capacity `κ ≥ 1` and every normalized monotone submodular `f` on `2^X`
(accessed only through value queries on subsets of `X`):
1. on every outcome of the tape, the run halts within `c (n + κ + 1)^d` steps (polynomial time),
   makes at most `C |X| κ` value queries, and outputs `A ⊆ X` with `|A| ≤ κ`;
2. the output is a random variable, and for every fixed legal future `h` of `f`,
   `E h(A) ≥ (2 − √2) max {h(O) : O ⊆ X, |O| ≤ κ}`.

**Formalization Note.** The law of `A` is determined by `P` and `f` alone, before `h`. One uniform
program for all `(X, κ)` is required, which implies the page's "for every `X` and `κ` there is an
algorithm" and gives "`O(|X| κ)`" and "polynomial time" their content. -/
theorem theorem_4_3 :
    ∃ C : ℝ, 0 < C ∧ ∃ (P : Program) (c d : ℕ), Admissible P ∧
      ∀ (n κ : ℕ), 1 ≤ κ → ∀ f : Finset (Fin n) → ℝ, PolyContract.IsRankFunction f →
        (∀ ω : ℕ → unitInterval, ∃ s A q,
          runStatic P (natFn f) n κ (c * (n + κ + 1) ^ d) ω = some (s, A, q) ∧
          (q : ℝ) ≤ C * (n : ℝ) * (κ : ℝ) ∧ A.card ≤ κ) ∧
        (∀ S : Finset ℕ,
          MeasurableSet {ω | staticOut P (natFn f) n κ (c * (n + κ + 1) ^ d) ω = S}) ∧
        ∀ h : Finset (Fin n) → ℝ, IsLegalFuture f h →
          (2 - Real.sqrt 2) * SharpConsist.OPTk κ h ≤
            ∫ ω, natFn h (staticOut P (natFn f) n κ (c * (n + κ + 1) ^ d) ω) ∂tape := by sorry

end SharpConsist.Supplement
