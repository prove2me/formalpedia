-- Prove2me | Theorems.Thm_RandomStreamCI_CodeIntersection_classical_lower_bound
-- name    : RandomStreamCI.CodeIntersection.classical_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:32:03.39902+00:00
-- url     : https://prove2.me/theorems/8d63791b-8f55-4785-825a-e042e6957fa4
-- title:
--   Theorem 18 — Exponential classical memory with exponentially small success
-- statement:
--   For the explicit folded code family of Proposition 7, there exist constants $c_1,c_2,a>0$ and $N$, chosen before every program, such that for every integer $n\ge N$ and every independent randomized one-pass classical program using at most $2^{c_1n^{c_2}}$ bits,
--
--   $$\Pr_{H,\pi,\mathrm{coins}}[B\text{ succeeds}]\le2^{-an}.$$
--
--   Here $H$ is uniform, $\pi$ is an independent uniform bijection enumerating the entire table, and the code family is fixed publicly. This preserves the exponentially small success conclusion throughout the full stretched-exponential memory range.
--
--   Differences from the source:
--   - encoding: coordinates and times numbered from one → Fin indices numbered from zero; reason: the order-preserving relabelling preserves every source instance
--   - encoding: explicit folded family and polynomial-time deterministic dual decoder with asymptotic bounds → published folded-evaluation image over publicly named finite fields, uniform finite Turing machines and eventual quantified growth bounds; reason: finite-field labels and polynomially equivalent unary encodings fix representations; all constants and thresholds are uniform in blocklength
--   - encoding: classical streaming algorithms, including independent private randomness → independent PMF mixtures of finite deterministic layered transducers with terminal word-or-failure outputs; reason: fixing coins selects a deterministic finite behavior, so arbitrary random tapes induce the same finite mixture
--   - encoding: exponential success bound and polynomial quantum memory with success one minus little-o of one → positive real constants and eventual inequalities, and a nonnegative error sequence tending to zero; reason: expands the asymptotic quantifiers without fixing unstated constants or discarding any ordering
--   - generalization: C is the folded Reed–Solomon code family of Proposition 7 → every code family F satisfying FamilyProperties F c c' (all conclusions of Proposition 7) for some 0 < c < c' < 1; reason: the source proof (pp. 16–17, (74)–(75)) uses only Proposition 7's list recovery, ρ, ℓ, L and the growth of log|C| and log M; the Proposition 7 family satisfies FamilyProperties (item explicit_folded_codes), so the statement specializes to the source's family
-- source:
--   Bouland–Ding–Jain, Exponential quantum space advantage in random data streams, STOC 2027 submission #71, preprint dated 2026-11-02, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/71.pdf, SHA256 3fe1835efedc1b9f29103379085d28d84ab1057dc30c3e3f05a8dce9f536a797, Theorem 18, printed p. 16 / PDF p. 16

import Definitions.Def_RandomStreamCI_CodeIntersection_Separation

noncomputable section

namespace RandomStreamCI.CodeIntersection

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Theorem 18, p. 16, with every asymptotic and machine quantifier expanded in ClassicalHard. -/
theorem classical_lower_bound (F : CodeFamily) (c c' : ℝ)
    (hc : 0 < c) (hcc : c < c') (hc' : c' < 1) (hF : FamilyProperties F c c') :
    ClassicalHard F := by sorry

end RandomStreamCI.CodeIntersection
