-- Prove2me | Theorems.Thm_RandomStreamCI_CodeIntersection_exponential_quantum_space_advantage
-- name    : RandomStreamCI.CodeIntersection.exponential_quantum_space_advantage
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:32:04.324738+00:00
-- url     : https://prove2.me/theorems/38b137e2-3773-42dc-8960-53287c33d8c9
-- title:
--   Theorem 1 — Exponential quantum space advantage for random-order Code Intersection
-- statement:
--   There exists an explicit folded Reed–Solomon code family with all the guarantees of Proposition 7 (taking $c=1/4$ and $c'=1/2$) for which both complete conclusions hold. There are $c_1,c_2,a>0$ and $N$ such that every classical one-pass program with at most $2^{c_1n^{c_2}}$ bits, for every $n\ge N$, satisfies
--
--   $$\Pr_{H,\pi,\mathrm{coins}}[B\text{ succeeds}]\le2^{-an}.$$
--
--   There is also one quantum one-pass family using polynomial total workspace, and nonnegative $\varepsilon_n\to0$, for which
--
--   $$\forall n\text{ sufficiently large}\ \forall\pi,\quad\Pr_{H,\mathrm{outcomes}}[Q_n\text{ succeeds}\mid\pi]\ge1-\varepsilon_n.$$
--
--   The oracle labels are independent fair bits and the complete table is streamed exactly once. The quantum algorithm has no post-pass oracle access. Code existence, explicitness, recovery and decoding are conclusions, not hypotheses. This is the joint separation of Theorems 18 and 28 underlying the informal headline.
--
--   Differences from the source:
--   - encoding: coordinates and times numbered from one → Fin indices numbered from zero; reason: the order-preserving relabelling preserves every source instance
--   - encoding: explicit folded family and polynomial-time deterministic dual decoder with asymptotic bounds → published folded-evaluation image over publicly named finite fields, uniform finite Turing machines and eventual quantified growth bounds; reason: finite-field labels and polynomially equivalent unary encodings fix representations; all constants and thresholds are uniform in blocklength
--   - encoding: classical streaming algorithms, including independent private randomness → independent PMF mixtures of finite deterministic layered transducers with terminal word-or-failure outputs; reason: fixing coins selects a deterministic finite behavior, so arbitrary random tapes induce the same finite mixture
--   - reading: quantum streaming algorithm with polynomial memory and unrestricted computation time → a family of finite-memory current-item-controlled CPTP maps and an input-independent final measurement, with dilation and output workspace charged; reason: the source does not specify a gate set or uniform circuit convention; this is the finite-dimensional bounded-workspace channel model, with no oracle access after the pass
--   - encoding: exponential success bound and polynomial quantum memory with success one minus little-o of one → positive real constants and eventual inequalities, and a nonnegative error sequence tending to zero; reason: expands the asymptotic quantifiers without fixing unstated constants or discarding any ordering
--   - encoding: the headline uses the family supplied by Proposition 7 → the goal selects the admissible exponents c = 1/4 and c prime = 1/2; reason: the headline asserts existence of a separation; the separate Proposition 7 item retains every 0 < c < c prime < 1
-- source:
--   Bouland–Ding–Jain, Exponential quantum space advantage in random data streams, STOC 2027 submission #71, preprint dated 2026-11-02, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/71.pdf, SHA256 3fe1835efedc1b9f29103379085d28d84ab1057dc30c3e3f05a8dce9f536a797, Theorem 1, printed p. 2 / PDF p. 2

import Definitions.Def_RandomStreamCI_CodeIntersection_Separation

noncomputable section

namespace RandomStreamCI.CodeIntersection

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Theorem 1, p. 2, in the full formal strength of Theorems 18 and 28. Existence of the explicit folded family is a conclusion. -/
theorem exponential_quantum_space_advantage :
    ∃ F : CodeFamily, FamilyProperties F (1 / 4) (1 / 2) ∧ ClassicalHard F ∧ QuantumEasy F := by sorry

end RandomStreamCI.CodeIntersection
