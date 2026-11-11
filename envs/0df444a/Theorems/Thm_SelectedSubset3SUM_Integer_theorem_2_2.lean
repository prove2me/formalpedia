-- Prove2me | Theorems.Thm_SelectedSubset3SUM_Integer_theorem_2_2
-- name    : SelectedSubset3SUM.Integer.theorem_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:51:37.532473+00:00
-- url     : https://prove2.me/theorems/d44fe713-862b-4025-803e-12cb0b526f24
-- title:
--   Theorem 2.2 — deterministic real-weight selected-entries subset convolution
-- statement:
--   Let $\mathcal A,\mathcal B$ be collections of $t$-element subsets of $[d]$, with arbitrary real weights $f,g$, extended by zero outside these collections. Assume $2t\le d$ and let $n\ge|\mathcal A|+|\mathcal B|$. For every query family $\mathcal C$ of $2t$-element subsets and every natural $s$ with $0\le s\le2t$, one uniform deterministic algorithm outputs every exact value $(f\star g)(X)$, $X\in\mathcal C$, in total time
--
--   $$K(d+1)^e\left(n+\sum_{j=0}^s\binom dj+|\mathcal C|\sum_{j=s}^{2t}\binom{2t}j\right).$$
--
--   The program, positive constant $K$, polynomial degree $e$ and word factor precede all input parameters, coefficients and queries. The assertion includes a real ring-arithmetic program and a word-RAM implementation for polynomially bounded integer coefficients, with the required coefficient bits supplied through the word-width convention. Both cutoff endpoints, $d=t=0$, empty supports and empty queries are included.
--
--   This is the full selected-query primitive supporting the integer reduction. It asserts correctness and charged execution, not merely an algebraic identity.
--
--   Differences from the source:
--   - reading: the undefined input-size symbol n in Theorem 2.2 → n is any upper bound on the sum of the two sparse support sizes; reason: this is the input-processing term used with n=N by Theorem 2.3; zero weights in the supplied support remain permitted
--   - encoding: arithmetic-operation complexity with word-RAM subset indices → finite exact-real ring programs and bounded-word integer programs, with charged instructions and input/output and sufficiently large word widths; reason: the scalar instructions are only exact addition, subtraction, multiplication and memory access; integer realization is asserted or proved, never assumed from finite real precision
--   - encoding: finite sets and set families → arbitrary-order duplicate-free lists, with subset masks on Fin d; reason: every finite-set instance has such a presentation; no sorting or disjointness promise is added and all presentation and output costs are charged
--   - encoding: d raised to an unspecified absolute polynomial power → K times (d+1)^e with one code and constants before n,d,t,s,weights and queries; reason: this makes the polynomial convention total at d=0 and retains both cutoff endpoints
-- source:
--   Timothy M. Chan, Reina Itakura, Zhiyuan Ma, Yuancheng Yu, STOC 2027 submission #1421 (October 2026), Theorem 2.2, p.5, proof continuing p.6, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1421.pdf

import Definitions.Def_SelectedSubset3SUM_Integer_SubsetMachine

namespace SelectedSubset3SUM.Integer

/-- Theorem 2.2, p.5 (proof through p.6): full real-weight selected-query tradeoff,
with its bounded-integer word-RAM realization. The input-size symbol n is read as an
upper bound on the total sparse support count. Constants precede every problem parameter. -/
theorem theorem_2_2 :
    ∃ (realCode : List ScalarInstr) (integerCode : List TrulySubcubicAPSP.Instr)
      (b e : ℕ) (K : ℝ),
      0 < b ∧ 0 < K ∧
      RealSelectedBound realCode b e K ∧ IntegerSelectedBound integerCode b e K := by sorry

end SelectedSubset3SUM.Integer
