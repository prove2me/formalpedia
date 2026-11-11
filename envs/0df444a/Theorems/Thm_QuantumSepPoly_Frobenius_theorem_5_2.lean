-- Prove2me | Theorems.Thm_QuantumSepPoly_Frobenius_theorem_5_2
-- name    : QuantumSepPoly.Frobenius.theorem_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:10:19.483303+00:00
-- url     : https://prove2.me/theorems/ddba1e7f-3f69-4cde-b37b-f759ace5eb12
-- title:
--   Theorem 5.2 — Dense Max-k-CSP PTAS
-- statement:
--   For every fixed arity $k$, nonempty finite alphabet of size $q$, and $\delta>0$, there is a randomized finite program and a polynomial bound uniform in the number of variables and the input payoff tables. Given a dense Max-$k$-CSP with ordered repeated tuples and predicates in $[0,1]$, it returns a valid assignment and, with probability at least $2/3$,
--   $$\operatorname{val}_I(z)\ge\operatorname{OPT}(I)-\delta.$$
--   The program halts within $C(n+1)^e$ charged operations almost surely. This is an algorithm-existence target, with the full input tables rather than an optimum oracle.
--
--   Differences from the source:
--   - encoding: coordinates labelled 1 through d → coordinates indexed by Fin d from 0 through d-1; reason: canonical relabelling preserves all vectors, matrices, sums, and constraints
--   - encoding: randomized polynomial-time algorithm in exact real arithmetic → finite scalar RAM program, product random tapes, measurable output, and a charged bound C(d+1)^k preceding every input; reason: makes the source runtime and probability claims operational without changing the continuous input domain
--   - encoding: any finite nonempty alphabet of fixed size → Fin q with q positive; reason: every finite nonempty alphabet is obtained by relabelling its symbols
-- source:
--   Giulio Malavolta, STOC 2027 submission #1577 (October 2026), Theorem 5.2, p. 19 (PDF p. 19); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1577.pdf

import Definitions.Def_QuantumSepPoly_Frobenius_AlgorithmIO

open MeasureTheory

namespace QuantumSepPoly.Frobenius

/-- Theorem 5.2, p.19: a uniform finite program for every fixed arity,
alphabet size, and accuracy. Tables, not their optimum, are the input. -/
theorem theorem_5_2 (k q : ℕ) (hq : 0 < q) (δ : ℝ) (hδ : 0 < δ) :
  ∃ (P : RAMProgram) (C : ℝ) (e : ℕ), 0 < C ∧
    ∀ (n : ℕ) (I : MaxCSP n k (Fin q)), CSPDense I → CSPBounded I →
      (∀ᵐ tape ∂tapeLaw, RAMTerminates P (cspInitial δ I) (C*(n+1)^e) tape) ∧
      (∀ tape, (∃ steps, (ramRun P tape (cspInitial δ I) steps).stopped = true) →
        ∃ z : Fin n → Fin q, CSPOutput P δ I tape z) ∧
      MeasurableSet {tape | ∃ z : Fin n → Fin q,
        CSPOutput P δ I tape z ∧ cspValue I z ≥ cspOPT I - δ} ∧
      tapeLaw {tape | ∃ z : Fin n → Fin q,
        CSPOutput P δ I tape z ∧ cspValue I z ≥ cspOPT I - δ} ≥ ENNReal.ofReal (2/3) := by sorry

end QuantumSepPoly.Frobenius
