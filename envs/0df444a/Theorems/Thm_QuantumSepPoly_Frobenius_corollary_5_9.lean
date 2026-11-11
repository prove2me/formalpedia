-- Prove2me | Theorems.Thm_QuantumSepPoly_Frobenius_corollary_5_9
-- name    : QuantumSepPoly.Frobenius.corollary_5_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:10:26.616413+00:00
-- url     : https://prove2.me/theorems/6f3e8cc2-dcf0-4aa5-8399-c80574dda77a
-- title:
--   Corollary 5.9 — polynomial-time Frobenius weak membership
-- statement:
--   For every fixed $0<\eta\le1$, there is one randomized finite exact-arithmetic program and constants $C>0$, $k\in\mathbb N$, independent of the dimension and input density matrix. For every $d\ge1$ and complex bipartite density $\rho$, the program halts within $C(d+1)^k$ charged operations almost surely and returns an accept/reject bit, with
--   $$\rho\in\operatorname{Sep}(d,d)\implies\Pr[\mathrm{accept}]\ge2/3,$$
--   $$\operatorname{distSep}_d(\rho)>\eta\implies\Pr[\mathrm{accept}]\le1/3.$$
--   The entire intermediate band is unpromised, the soundness gap stays strict, and arbitrary ranks and continuous complex entries are included. This is fixed-accuracy polynomial time, without a polynomial bound in inverse accuracy.
--
--   Differences from the source:
--   - encoding: coordinates labelled 1 through d → coordinates indexed by Fin d from 0 through d-1; reason: canonical relabelling preserves all vectors, matrices, sums, and constraints
--   - encoding: randomized polynomial-time algorithm in exact real arithmetic → finite scalar RAM program, product random tapes, measurable output, and a charged bound C(d+1)^k preceding every input; reason: makes the source runtime and probability claims operational without changing the continuous input domain
-- source:
--   Giulio Malavolta, STOC 2027 submission #1577 (October 2026), Corollary 5.9, p. 24 (PDF p. 24); Theorem 1.1, p. 2; Section 2.4, p. 8; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1577.pdf

import Definitions.Def_QuantumSepPoly_Frobenius_AlgorithmIO
import Definitions.Def_QuantumSepPoly_Frobenius_SeparableStates

open MeasureTheory

namespace QuantumSepPoly.Frobenius

/-- Corollary 5.9, p.24; Section 2.4, p.8 supplies both promise clauses.
Exact real arithmetic, continuous complex density inputs, and execution-based cost. -/
theorem corollary_5_9 (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) :
  ∃ (P : RAMProgram) (C : ℝ) (k : ℕ), 0 < C ∧
    ∀ (d : ℕ), 0 < d → ∀ (ρ : Bip d), IsDensity ρ →
      (∀ᵐ tape ∂tapeLaw, RAMTerminates P (matrixInitial η ρ) (C*(d+1)^k) tape) ∧
      (∀ tape, (∃ steps, (ramRun P tape (matrixInitial η ρ) steps).stopped = true) →
        ((ramResult P (matrixInitial η ρ) tape).real 1 = 0 ∨
         (ramResult P (matrixInitial η ρ) tape).real 1 = 1)) ∧
      MeasurableSet {tape | accepts P η ρ tape} ∧
      (ρ ∈ Sep d → tapeLaw {tape | accepts P η ρ tape} ≥ ENNReal.ofReal (2/3)) ∧
      (distanceSep ρ > η → tapeLaw {tape | accepts P η ρ tape} ≤ ENNReal.ofReal (1/3)) := by sorry

end QuantumSepPoly.Frobenius
