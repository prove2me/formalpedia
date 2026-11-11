-- Prove2me | Theorems.Thm_QuantumSepPoly_Frobenius_theorem_5_7
-- name    : QuantumSepPoly.Frobenius.theorem_5_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:10:22.383714+00:00
-- url     : https://prove2.me/theorems/41116a86-f1ed-4bf8-8981-c8afa16bc7f0
-- title:
--   Theorem 5.7 — Product-state approximation algorithm
-- statement:
--   For every fixed $0<\tau\le1$, there is a randomized finite program, a constant $C>0$, and a natural exponent $k$, uniform for all $d\ge1$ and Hermitian $M$ with $\|M\|_F\le1$. It halts within $C(d+1)^k$ charged operations almost surely, returns unit vectors $x,y$, and satisfies
--   $$\Pr[(x\otimes y)^*M(x\otimes y)\ge h_{\rm Sep}(M)-\tau]\ge2/3.$$
--   The output pair is decoded from execution. No zero-partial-trace restriction is imposed on the input. This is the optimization algorithm used by weak membership.
--
--   Differences from the source:
--   - encoding: coordinates labelled 1 through d → coordinates indexed by Fin d from 0 through d-1; reason: canonical relabelling preserves all vectors, matrices, sums, and constraints
--   - encoding: randomized polynomial-time algorithm in exact real arithmetic → finite scalar RAM program, product random tapes, measurable output, and a charged bound C(d+1)^k preceding every input; reason: makes the source runtime and probability claims operational without changing the continuous input domain
-- source:
--   Giulio Malavolta, STOC 2027 submission #1577 (October 2026), Theorem 5.7, p. 21 (PDF p. 21); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1577.pdf

import Definitions.Def_QuantumSepPoly_Frobenius_AlgorithmIO
import Definitions.Def_QuantumSepPoly_Frobenius_SeparableStates

open MeasureTheory

namespace QuantumSepPoly.Frobenius

/-- Theorem 5.7, pp.21–22. Program and polynomial bound precede dimension
and matrix. Every Hermitian Frobenius-bounded input and every d>=1 is included. -/
theorem theorem_5_7 (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
  ∃ (P : RAMProgram) (C : ℝ) (k : ℕ), 0 < C ∧
    ∀ (d : ℕ), 0 < d → ∀ (M : Bip d), M.IsHermitian → frob M ≤ 1 →
      (∀ᵐ tape ∂tapeLaw, RAMTerminates P (matrixInitial τ M) (C*(d+1)^k) tape) ∧
      (∀ tape, (∃ steps, (ramRun P tape (matrixInitial τ M) steps).stopped = true) →
        vecSq (productOutput P τ M tape).1 = 1 ∧ vecSq (productOutput P τ M tape).2 = 1) ∧
      Measurable (productOutput P τ M) ∧
      tapeLaw {tape | productValue M (productOutput P τ M tape).1 (productOutput P τ M tape).2 ≥
        support M - τ} ≥ ENNReal.ofReal (2/3) := by sorry

end QuantumSepPoly.Frobenius
