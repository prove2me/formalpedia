-- Prove2me | Theorems.Thm_SketchAttr_LOO_theorem_5_1
-- name    : SketchAttr.LOO.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T15:31:26.057259+00:00
-- url     : https://prove2.me/theorems/0e522fa2-3c72-410a-8437-8c683d57246a
-- title:
--   Theorem 5.1 — all LOO values, work, space and calls (corrected: N=1 work bound)
-- statement:
--   There exist a main program $M$, a call implementation $S$, and one universal constant $C>0$ with the following guarantees. Let $n\ge1$, and let $\phi:\mathbb C^n\to\mathbb C$ be an arithmetic circuit real-valued on $[0,1]^n$. Fix $\varepsilon,\delta\in(0,1)$ and take the rounded parameters $N,K,m,k$ from the Execution definition.
--
--   1. For every Gaussian tape, the composed execution halts without fault within $C\operatorname{size}(\phi)(mN\log(N+1)+K)$ instructions and writes at most $C(\operatorname{size}(\phi)N+nmN)$ auxiliary cells. Every completed call returns the true value, gradient and requested directional derivatives.
--   2. For every stability profile $\alpha$ with $\phi$ $\alpha$-stable and $\alpha(4)<\infty$, the estimates obey
--   $$\mathbb P\left(\exists i\in[n]:|\widehat L_i-\phi(e_i)|>\varepsilon\alpha(4)\right)\le\delta.$$
--   3. For every tape, the number of calls is exactly
--   $$\min\{n,m+K\}.$$
--
--   The paper writes the work, space and call bounds as $\widetilde O(\operatorname{size}(\phi)\log(n/\delta)/\varepsilon)$, $\widetilde O(\operatorname{size}(\phi)+n\log(n/\delta)/\varepsilon)$ and $\widetilde O(\min\{n,\log(n/\delta)/\varepsilon\})$; its proof on p. 18 yields the explicit bounds above. Work and space do not require stability. One theorem contains all three clauses, and programs and constant precede every instance.
--
--   **Formalization Note** The main program sees only parameters. It accesses the circuit solely through the actual finite call program, whose steps and writes are included. The returned estimates need not be constrained in advance to the particular implementation of Algorithm 1: the source theorem asserts existence of an algorithm. Probability is outer measure of the bad set.
--
--   Differences from the source:
--   - reading: integer-valued N=log_4(1/epsilon), K=1/epsilon, m=(256/epsilon) log(32nN/delta), k=log(32nN/delta) written without rounding → ceilings for N, K and m and the floor for k; reason: these choices preserve arbitrary epsilon and delta in (0,1), give 4^(-N) <= epsilon and 4^(N-1) <= 1/epsilon, and match Proposition 4.8
--   - reading: exact complex arithmetic and constant-time random-access storage with no fixed machine → the finite two-program complex RAM in Machine with scalar Gaussian samples and counted subroutine steps and writes; reason: this pins down Section 3.2 and the oracle access convention without a primitive gradient or hidden circuit access
--   - correction: p. 18 proof work scale size(phi)(m N log N + K) → size(phi)(m N log(N+1) + K); reason: the supporting sketch bound size(phi) N log N is zero at N=1 although f(w)=(a+b)*w1 with arbitrary input-circuit literals a,b needs their sum; log(N+1) repairs that boundary and is within a universal factor for N>=2
--   - encoding: positive input dimension, extended profile alpha(4), and probability at least 1-delta of simultaneous accuracy → Fin n with n>=1, toReal under alpha(4)<infinity, and an outer-measure upper bound on the strict bad set; reason: indices change only their base, the profile is finite where converted, and the bad-set bound preserves the full simultaneous guarantee
--   - encoding: the proof uniform O work and space bounds and min(n,m+K) calls → one positive real C shared by work and space, a floor of the real instruction budget, and exact call equality; reason: a larger universal constant bounds both resource scales; integer steps within the floor are exactly steps within the real budget
-- source:
--   Liaw, Mehta, Velegkas, Zhou, Sketching Language Models for Context Attribution, STOC 2027 submission #9 (PDF sha256 86af2569e45c55b1009e7453d4f53047b5820d44868a7f528bdb6fed1a2ef0e2), p. 14, Theorem 5.1, all clauses; pp. 15–18, proof and Algorithm 1; p. 19, oracle access; canonical PDF: https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/9.pdf

import Mathlib
import Definitions.Def_SketchAttr_LOO_Execution
open scoped ENNReal

namespace SketchAttr.LOO

/-- Theorem 5.1, all three clauses, with p.18's explicit complexity bounds.
Programs and the constant are uniform over the instance.
Boundary correction: the supporting sketch work bound N * log N on pp.12,18
vanishes at N=1. For the input circuit f(w)=(a+b)*w₁ with arbitrary
real literals a,b, even the constant gradient coefficient requires a+b.
The work scale uses N * log (N+1), as recorded in the mission's HARD.md; for N>=2
the two scales differ by a universal factor. -/
theorem theorem_5_1 :
    ∃ (M S : Program) (C : ℝ), 0 < C ∧
      ∀ (n : ℕ), 1 ≤ n → ∀ (c : Circuit n 1), c.RealOnCube →
      ∀ (ε δ : ℝ), 0 < ε → ε < 1 → 0 < δ → δ < 1 →
        (∀ tape : ℕ → ℂ,
          let result := executionResult M S C c ε δ tape
          result.halted = true ∧ result.fault = false ∧ result.inCall = false ∧
          (result.space : ℝ) ≤ C * spaceScale c ε δ ∧
          result.calls = min n (sampleParameter n ε δ + exactParameter ε) ∧
          CorrectCalls c M S (executionInput c ε δ) tape (executionFuel C c ε δ)) ∧
        (∀ α : StabilityProfile,
          IsStable (circuitFunction c) α → α ⟨4, by norm_num⟩ < ⊤ →
          gaussianTape (failureSet M S C c ε δ α) ≤ ENNReal.ofReal δ) := by sorry

end SketchAttr.LOO
