-- Prove2me | Theorems.Thm_QuantumSepPoly_Frobenius_lemma_4_1
-- name    : QuantumSepPoly.Frobenius.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:10:56.290657+00:00
-- url     : https://prove2.me/theorems/c9494a6a-a623-4bc7-87f0-8921c2496817
-- title:
--   Lemma 4.1 — Flat bounded-amplitude near-optimizers
-- statement:
--   Let $M$ be Hermitian with zero partial traces and $d^2\|M\|_{\max}\le\gamma$. The source parameter functions $\kappa,\Delta$ have uniform polynomial upper bounds in $\gamma,1/\eta$. For $0<\eta<1$ and $d\ge\Delta$,
--   $$\max_{\|x\|_2=\|y\|_2=\sqrt d}Q_M(x,y)\le\max_{\substack{\|x\|_2=\|y\|_2=\sqrt d\\\|x\|_\infty,\|y\|_\infty\le\kappa}}Q_M(x,y)+\eta.$$
--   Here $Q_M=d^{-2}(x\otimes y)^*M(x\otimes y)$. This bounds the amplitude needed by near-optimizers.
--
--   Differences from the source:
--   - encoding: coordinates labelled 1 through d → coordinates indexed by Fin d from 0 through d-1; reason: canonical relabelling preserves all vectors, matrices, sums, and constraints
--   - encoding: polynomially bounded kappa and Delta and attained maxima → the parameter formulas on pp.15–16, uniform coefficient-degree upper bounds, and suprema of exactly the feasible sets; reason: attainment and nonempty bounded domains are exposed in the separate optimization geometry target
-- source:
--   Giulio Malavolta, STOC 2027 submission #1577 (October 2026), Lemma 4.1, p. 13 (PDF p. 13); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1577.pdf

import Definitions.Def_QuantumSepPoly_Frobenius_Quartic

namespace QuantumSepPoly.Frobenius

/-- Lemma 4.1, p.13, with the actual parameter choices on pp.15–16.
The polynomial bound is uniform in dimension, gamma, and accuracy. -/
theorem lemma_4_1 : ∃ (C : ℝ) (k : ℕ), 0 < C ∧
  ∀ γ η : ℝ, 0 ≤ γ → 0 < η → η < 1 →
    kappaParam γ η ≤ C*(1+γ+1/η)^k ∧ deltaParam γ η ≤ C*(1+γ+1/η)^k ∧
    ∀ (d : ℕ), 0 < d → deltaParam γ η ≤ d → ∀ (M : Bip d), FlatInput M γ →
      sphereValue M ≤ boundedSphereValue M (kappaParam γ η) + η := by sorry

end QuantumSepPoly.Frobenius
