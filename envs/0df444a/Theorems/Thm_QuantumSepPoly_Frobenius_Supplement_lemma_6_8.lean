-- Prove2me | Theorems.Thm_QuantumSepPoly_Frobenius_Supplement_lemma_6_8
-- name    : QuantumSepPoly.Frobenius.Supplement.lemma_6_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T11:54:49.731616+00:00
-- url     : https://prove2.me/theorems/71482f64-4976-4af8-8d3d-a7cce4992b81
-- title:
--   Lemma 6.8 — Joint sampling success and Frobenius approximation
-- statement:
--   Fix a positive-size sparse Boolean CSP, a fully satisfying law $D$, and one finite sampler program with saved construction memory. For every $S$ with $|S|\le n+m+2$, assume exactly the Lemma 6.4 marginal law for that same $D$, measurability, and expected execution cost at most $CL^e$ with $C>0$. Fix source-admissible parameters and the branch $4k\le n+m+2$, and use the source computed sample count and independent calls. Then
--   $$\Pr\left\{\text{sampling finishes within }200s(N|\Omega|)^{4k}CL^e\ \text{and}\ \|\omega-\psi\|_F\le\frac{\varepsilon}{32(N|\Omega|)^{2k}}\right\}\ge98/100.$$
--   The probability is over sampling after any fixed construction outcome. The timeout and error event are one conjunction, not separately conditioned guarantees.
--
--   Differences from the source:
--   - generalization: satisfiable formula and the distribution supplied by Lemma 6.4 → any sparse Boolean CSP and any fully satisfying assignment law satisfying the stated sampler context where needed; reason: the constructed CSP and its single law D satisfy these hypotheses, so every source instance is included
--   - encoding: polynomial or soft-exponential arithmetic time → positive coefficient and natural exponent witnesses with L=n+m+2, before every input and random run; reason: this unpacks the source asymptotic orders uniformly and includes finite input/output serialization
--   - encoding: finite complex registers with one-based indices → zero-based finite function registers and explicit mixed-radix basis maps; reason: bijections preserve the source matrices and the specified bipartite cut
--   - encoding: expected sampler runtime → the lower integral of first-halting cost, with infinity on nontermination; reason: the nonnegative extended integral has no nonintegrable-to-zero default
-- source:
--   Giulio Malavolta, STOC 2027 submission #1577 (October 2026), Lemma 6.8, p. 30 (PDF p. 30); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1577.pdf

import Definitions.Def_QuantumSepPoly_Frobenius_Supplement_Sampling

open scoped BigOperators ENNReal

namespace QuantumSepPoly.Frobenius.Supplement

theorem lemma_6_8 (N A δ n m : ℕ) (η ξ C : ℝ) (e t : ℕ) (ε : ℚ)
    (I : MaxCSP N 2 (Fin A)) (D : PMF (Fin N → Fin A))
    (P : RAMProgram) (s₀ : RAMState) (hA : 0 < A) (hN : 1 ≤ N)
    (hI : Sparse I δ) (hη : 0 < η ∧ η < 1) (hC : 0 < C)
    (hp : Admissible η A δ ξ t ε)
    (hbranch : 4*registerCount N A ε ≤ n+m+2)
    (hD : ∀ z, D z ≠ 0 → cspValue I z = 1)
    (hSample : ∀ S : Finset (Fin N), S.card ≤ n+m+2 →
      Measurable (sampleOutput hA P s₀ S) ∧
      (∀ a : S → Fin A, tapeLaw {r | sampleOutput hA P s₀ S r = a} =
        D.toMeasure {z | (fun i : S => z i) = a}) ∧
      (∫⁻ r, executionCost P (sampleInitial s₀ S) r ∂tapeLaw) ≤
        ENNReal.ofReal (polyBound C e n m)) :
    ENNReal.ofReal (98/100 : ℝ) ≤ tapeLaw {r |
      SamplingEvent hA P s₀ (registerCount N A ε)
        (sampleCount N A (registerCount N A ε) ε) ε (polyBound C e n m) D r} := by sorry

end QuantumSepPoly.Frobenius.Supplement
