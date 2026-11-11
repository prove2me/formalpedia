-- Prove2me | Theorems.Thm_RandomStreamCI_CodeIntersection_quantum_upper_bound
-- name    : RandomStreamCI.CodeIntersection.quantum_upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:32:11.507107+00:00
-- url     : https://prove2.me/theorems/1aec8e7b-f5ad-403b-9d8c-52fc3a6f11ce
-- title:
--   Theorem 28 — Polynomial quantum memory for every fixed ordering
-- statement:
--   For the same folded family from Proposition 7, there exists one quantum one-pass program family, constants $K>0$ and integer $d$, a threshold $N$, and nonnegative errors $\varepsilon_n\to0$, such that
--
--   $$\forall n\ge N\ \forall\pi,\quad\mathrm{memory}(Q_n)\le Kn^d,\qquad\Pr_{H,\mathrm{outcomes}}[Q_n\text{ succeeds}\mid\pi]\ge1-\varepsilon_n.$$
--
--   The programs, constants and error sequence precede the ordering quantifier. Preparation, persistent classical registers, operation environments and final output workspace are charged. All failures remain in the original outcome distribution and no oracle access occurs after the pass. The conclusion is a complete solver rather than successful state preparation alone.
--
--   Differences from the source:
--   - encoding: coordinates and times numbered from one → Fin indices numbered from zero; reason: the order-preserving relabelling preserves every source instance
--   - encoding: explicit folded family and polynomial-time deterministic dual decoder with asymptotic bounds → published folded-evaluation image over publicly named finite fields, uniform finite Turing machines and eventual quantified growth bounds; reason: finite-field labels and polynomially equivalent unary encodings fix representations; all constants and thresholds are uniform in blocklength
--   - reading: quantum streaming algorithm with polynomial memory and unrestricted computation time → a family of finite-memory current-item-controlled CPTP maps and an input-independent final measurement, with dilation and output workspace charged; reason: the source does not specify a gate set or uniform circuit convention; this is the finite-dimensional bounded-workspace channel model, with no oracle access after the pass
--   - encoding: exponential success bound and polynomial quantum memory with success one minus little-o of one → positive real constants and eventual inequalities, and a nonnegative error sequence tending to zero; reason: expands the asymptotic quantifiers without fixing unstated constants or discarding any ordering
--   - generalization: C is the folded Reed–Solomon code family of Proposition 7 → every code family F satisfying FamilyProperties F c c' (all conclusions of Proposition 7) for some 0 < c < c' < 1; reason: the source proof (p. 28) uses only Proposition 7's dual decoding (14) and the linear folded structure, which FamilyProperties carries; the Proposition 7 family satisfies FamilyProperties (item explicit_folded_codes), so the statement specializes to the source's family
-- source:
--   Bouland–Ding–Jain, Exponential quantum space advantage in random data streams, STOC 2027 submission #71, preprint dated 2026-11-02, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/71.pdf, SHA256 3fe1835efedc1b9f29103379085d28d84ab1057dc30c3e3f05a8dce9f536a797, Theorem 28, printed p. 28 / PDF p. 28

import Definitions.Def_RandomStreamCI_CodeIntersection_Separation

noncomputable section

namespace RandomStreamCI.CodeIntersection

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Theorem 28, p. 28, with every asymptotic and machine quantifier expanded in QuantumEasy. -/
theorem quantum_upper_bound (F : CodeFamily) (c c' : ℝ)
    (hc : 0 < c) (hcc : c < c') (hc' : c' < 1) (hF : FamilyProperties F c c') :
    QuantumEasy F := by sorry

end RandomStreamCI.CodeIntersection
