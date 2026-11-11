-- Prove2me | Theorems.Thm_QuantumSepPoly_Frobenius_lemma_4_4
-- name    : QuantumSepPoly.Frobenius.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:11:52.514094+00:00
-- url     : https://prove2.me/theorems/3afdbd6f-d8ce-47d5-9ad8-575d64aae7b0
-- title:
--   Lemma 4.4 — Dimension-free discretization
-- statement:
--   For every $\gamma\ge0$ and $0<\eta<1$, the source functions $\kappa,\lambda,1/\varepsilon,\Delta$ have uniform polynomial upper bounds in $\gamma,1/\eta$, with the first three positive. For every Section 4 flat matrix and every finite $\varepsilon$-net $E$ contained in the radius-$\kappa$ disk, if $d\ge\Delta$, then
--   $$\left|\max_{\|x\|_2=\|y\|_2=\sqrt d}Q_M(x,y)-\max_{x,y\in E^d}\Lambda_M(x,y)\right|\le\eta.$$
--   Both directions of this absolute error estimate are part of the target.
--
--   Differences from the source:
--   - encoding: coordinates labelled 1 through d → coordinates indexed by Fin d from 0 through d-1; reason: canonical relabelling preserves all vectors, matrices, sums, and constraints
--   - encoding: four polynomially bounded parameters and maxima → the p.17 formulas with uniform coefficient-degree bounds and feasible-set suprema; reason: every finite net contained in the disk is covered and the separate geometry target supplies attainment
-- source:
--   Giulio Malavolta, STOC 2027 submission #1577 (October 2026), Lemma 4.4, p. 17 (PDF p. 17); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1577.pdf

import Definitions.Def_QuantumSepPoly_Frobenius_DiskNet

namespace QuantumSepPoly.Frobenius

/-- Lemma 4.4, p.17. Every finite disk net is covered, not just a selected mesh. -/
theorem lemma_4_4 : ∃ (C : ℝ) (k : ℕ), 0 < C ∧
  ∀ γ η : ℝ, 0 ≤ γ → 0 < η → η < 1 →
    0 < discKappa γ η ∧ 0 < discLambda γ η ∧ 0 < discEpsilon γ η ∧
    discKappa γ η ≤ C*(1+γ+1/η)^k ∧ discLambda γ η ≤ C*(1+γ+1/η)^k ∧
    1/discEpsilon γ η ≤ C*(1+γ+1/η)^k ∧ discDelta γ η ≤ C*(1+γ+1/η)^k ∧
    ∀ (d : ℕ), 0 < d → discDelta γ η ≤ d → ∀ (M : Bip d), FlatInput M γ →
      ∀ E : Finset ℂ, IsDiskNet E (discKappa γ η) (discEpsilon γ η) →
        |sphereValue M - discreteValue M (discLambda γ η) E| ≤ η := by sorry

end QuantumSepPoly.Frobenius
