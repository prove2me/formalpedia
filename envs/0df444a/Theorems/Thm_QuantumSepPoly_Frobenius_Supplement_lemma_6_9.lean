-- Prove2me | Theorems.Thm_QuantumSepPoly_Frobenius_Supplement_lemma_6_9
-- name    : QuantumSepPoly.Frobenius.Supplement.lemma_6_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T11:55:37.904061+00:00
-- url     : https://prove2.me/theorems/8608f57f-66c4-440c-8e27-78d443e98ccc
-- title:
--   Lemma 6.9 — Separable smoothing and positive-semidefinite domination
-- statement:
--   Use a positive-size sparse Boolean CSP, a fully satisfying law $D$, source-admissible parameters and the large-input branch. Let $\omega$ be the matrix from the actual finite sampler calls, with positive time-bound parameter $p$. On the entire good event of Lemma 6.8, including sampling success and its stated Frobenius error,
--   $$\widehat\omega\in\operatorname{Sep}((N|\Omega|)^k,(N|\Omega|)^k),\qquad\widehat\omega\succeq(1-\varepsilon/4)\psi.$$
--   Both separability and positive-semidefinite domination are conclusions. No sampler correctness or density conclusion is used to define the empirical state.
--
--   Differences from the source:
--   - generalization: satisfiable formula and the distribution supplied by Lemma 6.4 → any sparse Boolean CSP and any fully satisfying assignment law satisfying the stated sampler context where needed; reason: the constructed CSP and its single law D satisfy these hypotheses, so every source instance is included
--   - encoding: finite complex registers with one-based indices → zero-based finite function registers and explicit mixed-radix basis maps; reason: bijections preserve the source matrices and the specified bipartite cut
-- source:
--   Giulio Malavolta, STOC 2027 submission #1577 (October 2026), Lemma 6.9, p. 31 (PDF p. 31); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1577.pdf

import Definitions.Def_QuantumSepPoly_Frobenius_Supplement_Sampling

open scoped BigOperators ENNReal ComplexOrder

namespace QuantumSepPoly.Frobenius.Supplement

theorem lemma_6_9 (N A δ n m : ℕ) (η ξ p : ℝ) (t : ℕ) (ε : ℚ)
    (I : MaxCSP N 2 (Fin A)) (D : PMF (Fin N → Fin A))
    (P : RAMProgram) (s₀ : RAMState) (hA : 0 < A) (hN : 1 ≤ N)
    (hp₀ : 0 < p) (hI : Sparse I δ) (hη : 0 < η ∧ η < 1)
    (hp : Admissible η A δ ξ t ε)
    (hbranch : 4*registerCount N A ε ≤ n+m+2)
    (hD : ∀ z, D z ≠ 0 → cspValue I z = 1)
    (r : RandomTape)
    (hevent : SamplingEvent hA P s₀ (registerCount N A ε)
      (sampleCount N A (registerCount N A ε) ε) ε p D r) :
    let k := registerCount N A ε
    let ω := empiricalState hA P s₀ k (sampleCount N A k ε) r
    flatten (smooth ε ω) ∈ Sep ((N*A)^k) ∧
      (smooth ε ω - (1-(ε : ℝ)/4) • idealState k D).PosSemidef := by sorry

end QuantumSepPoly.Frobenius.Supplement
