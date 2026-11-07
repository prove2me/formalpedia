-- Prove2me | Theorems.Thm_SamplingLLL_theorem_2_6
-- name    : SamplingLLL.theorem_2_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:00:37.922753+00:00
-- url     : https://prove2.me/theorems/a4b24f86-bae5-4c94-b90c-51e9dcc98d18
-- title:
--   Theorem 2.6, p.8 — Sampling Local Lemma: FPRAS, perfect sampler, $O(|A|^2)$ expected recursive calls
-- statement:
--   Let an atomic product-space CSP have bounds $p_a\ge\lambda(\mathrm{Bad}_a)$, let $G$ be a set of events that are sampling-good with respect to these bounds, and let rational $x_a\in(0,1)$ satisfy
--   $$
--   4p_a\le x_a\prod_{b\in\Gamma_{H_G}(a)}(1-x_b)\qquad(a\in A). \tag{SLL}
--   $$
--   Then, for absolute constants $C,d,K$ and the explicit procedures of Appendices A and G, which read the instance, $G$ and $x$ but never $p$:
--   1. $Z>0$;
--   2. the sampler terminates almost surely, with law exactly $\mu$;
--   3. its expected running time is at most $C(L+1)^d$, for the input length $L$;
--   4. its expected number of recursive calls is at most $C|A|^2$;
--   5. for every rational $\varepsilon\in(0,1]$, the FPRAS terminates almost surely, runs in time at most $C((L+\mathrm{bits}(\varepsilon)+1)\lceil1/\varepsilon\rceil)^d$ on every run, and with probability at least $3/4$ outputs $\hat Z$ with $(1-\varepsilon)Z\le\hat Z\le(1+\varepsilon)Z$.
--
--   This is the paper's main result: at the scale of the local lemma, atomic events whose connected joint occurrences decay geometrically are charged only for their first neighbourhood.
--
--   **Formalization Note** The procedure is defined in Lean, so the claim about recursive calls has meaning, which it would not for a program chosen by an existential quantifier. Running time is ticks under the explicit charges: rational operations by the bit length of their actual operands, coins from fair bits, combinatorial steps by a fixed power of $L$.
--
--   Differences from the source:
--   - reading: "has an FPRAS", "has an expected-polynomial-time perfect sampler", "the sampler makes $O(|A|^2)$ recursive calls" → all clauses about the one explicit procedure of Appendices A and G, written in Lean, with no existential quantifier over programs; reason: clause 4 has no meaning for a program chosen by an existential; the explicit statement is stronger than existence of a program
--   - reading: running times "polynomial in the input length"; no machine named; "bit operations", p.10 → ticks of the explicit procedure under a charge table: rational operations by actual operand bits, exact coins from fair bits, $L^3$ per search step, $L$ per test and move; reason: the cost model of a bit-cost reading; audited in the moderation notes
--   - reading: "polynomial in ... the inverse relative error for counting", FPRAS with no stated confidence → worst-case time under a work cap $K((L+\mathrm{bits}(\varepsilon)+1)\lceil1/\varepsilon\rceil)^d$ for every rational $\varepsilon\in(0,1]$, including the bits of $\varepsilon$, and success probability at least $3/4$ with error $\varepsilon$; reason: p.25 gives the cap, $3/4$, and the error $\varepsilon/2$; a rational $\varepsilon$ near $1$ can have long bits and small $1/\varepsilon$, and "input length" covers them
--   - reading: recursive calls not specified further; "for each occurrence" → one invocation of an insertion kernel, a deletion kernel or a reciprocal coin, each counted once; all child coins of an experiment requested, without stopping at the first failure; reason: p.15 defines the counted calls with multiplicity; requesting all coins is the count in (7), the larger of the two the text allows
--   - encoding: the fixed orders of the proof, and finite domains $\Omega_v$ → index order of `Fin m`; $\Omega_v=\mathrm{Fin}(\mathrm{dom}_v+1)$; reason: the statement is for every instance, and every instance relabels to these
-- source:
--   Achlioptas, Counting and Sampling by Local Repair: From the Lovász Local Lemma to Random k-SAT, STOC 2027 submission (manuscript sha256 7a943167…), Theorem 2.6, p.8

import Mathlib
import Definitions.Def_SamplingLLL_sllAnalysis

set_option autoImplicit false

open scoped ENNReal

namespace SamplingLLL

open Proc

/-- Theorem 2.6 (Sampling Local Lemma), p.8. For every atomic product-space CSP, specified set `G`, rational
witnesses `x_a ∈ (0,1)`, and real numbers `p_a ≥ λ(Bad_a)` with (C) on `G` and (SLL): `Z > 0`; the sampler
terminates almost surely with law exactly `μ`; its expected ticks are polynomial in the input length; its
expected number of recursive calls is `O(|A|²)`; and for every rational `ε ∈ (0,1]`, the FPRAS has relative
error `ε` with probability at least `3/4`, in worst-case time polynomial in the input length, in the bit length
of `ε`, and in `1/ε`.

Source: Achlioptas, STOC 2027 submission (manuscript sha256 7a943167…), Theorem 2.6, p.8.

**Formalization Note.** The clauses are about one explicit procedure, `sampler` (and `fpras`), not about a
program chosen by `∃`, because "the sampler makes `O(|A|²)` recursive calls" says nothing of a program that may
inline its calls. Costs are bit costs by the charge table of `Proc`, `Primitives` and `sllData`: rationals by
their actual operand bits, coins from fair bits, combinatorial steps by a fixed power of `L`. The numbers `p`
are not an argument of `sampler`, `sllData` or `fpras`. `C`, `d`, `K` are absolute; `d` is the universal polynomial
degree. `K` and `d` enter `fpras` through its work cap (p.25). A call is one invocation of an insertion kernel,
a deletion kernel or a reciprocal coin (p.15). -/
theorem theorem_2_6 : ∃ C d K : ℕ, ∀ {n m : ℕ} (I : AtomicCSP n m) (G : Finset (Fin m))
    (x : Fin m → ℚ) (p : Fin m → ℝ), (∀ a, 0 < x a ∧ x a < 1) →
    (∀ a, ((I.badProb a : ℚ) : ℝ) ≤ p a) → (∀ a ∈ G, I.SamplingGood p a) → I.SLL G p x →
    0 < I.toCSP.Z Finset.univ ∧
    mass (I.sampler G x) = 1 ∧
    (∀ y, law (I.sampler G x) y = ENNReal.ofReal ((I.toCSP.mu Finset.univ y : ℚ) : ℝ)) ∧
    expTicks (I.sampler G x) ≤ ((C * (I.inputSize x + 1) ^ d : ℕ) : ℝ≥0∞) ∧
    expCalls (I.sampler G x) ≤ ((C * m ^ 2 : ℕ) : ℝ≥0∞) ∧
    ∀ ε : ℚ, 0 < ε → ε ≤ 1 →
      mass (I.fpras G x K d ε) = 1 ∧
      (∀ r, I.fpras G x K d ε r ≠ 0 →
        r.2.1 ≤ C * ((I.inputSize x + bits ε + 1) * ⌈(1 / ε : ℚ)⌉₊) ^ d) ∧
      (3 / 4 : ℝ≥0∞) ≤ probOf (I.fpras G x K d ε) fun Zh =>
        (1 - ε) * I.toCSP.Z Finset.univ ≤ Zh ∧ Zh ≤ (1 + ε) * I.toCSP.Z Finset.univ := by sorry

end SamplingLLL
