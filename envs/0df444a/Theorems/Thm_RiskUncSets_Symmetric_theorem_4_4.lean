-- Prove2me | Theorems.Thm_RiskUncSets_Symmetric_theorem_4_4
-- name    : RiskUncSets.Symmetric.theorem_4_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T12:29:06.912839+00:00
-- url     : https://prove2.me/theorems/84e88907-7d7d-4a7a-8c45-6b04d5c74e46
-- title:
--   Theorem 4.4: centrally symmetric distortion risk measures are mixtures of explicit generators
-- statement:
--   Fix $N\ge1$. A risk functional $\mu$ on the $N$ equiprobable observations has a representation $\mu=\mu_q$ for some nonincreasing probability vector $q$ whose permutohull is centrally symmetric about the sample mean for every dimension and every data set if and only if it is a convex mixture of the $\widehat N=\lfloor N/2\rfloor+1$ explicit generator risk measures:
--
--   $$
--   \mu(X)=\sum_{j=1}^{\widehat N}\lambda_j\mu_{\bar q^{j}}(X),
--   \qquad \lambda_j\ge0,\quad\sum_{j=1}^{\widehat N}\lambda_j=1
--   \quad\text{for every }X.
--   $$
--
--   Here $\mu_q(X)=-\sum_iq_ix_{(i)}$ uses increasing order statistics, and $\bar q^{j}$ is the three-level vector in equation (10). The theorem classifies the distortion risk measures that always induce centrally symmetric uncertainty sets.
--
--   **Formalization Note** Theorem 4.2 of the paper identifies the functionals $\mu_q$ with the distortion risk measures under the uniform law of Assumption 4.1. This mission states that parametrization directly because Theorem 4.2 is a draft in the companion mission and cannot be imported. The conclusion imposes no prior symmetry or mixture condition on $q$. The source prints $\widehat\mu_j$ in the mixture but defines $\mu_j$; both denote the risk measure of $\bar q^{j}$. Lean quantifies over all dimensions and data sets and covers even as well as odd $N$.
-- source:
--   Bertsimas & Brown, Constructing uncertainty sets for robust linear optimization, Oper. Res. 57(6) (2009), p. 1491, Theorem 4.4 and equation (10); DOI 10.1287/opre.1080.0646

import Definitions.Def_RiskUncSets_Symmetric_Setting

namespace RiskUncSets.Symmetric

theorem theorem_4_4 {N : ℕ} (hN : 0 < N)
    (μ : (Fin N → ℝ) → ℝ) :
    (∃ q ∈ restrictedSimplex N,
      (∀ X, μ X = muQ q X) ∧
      ∀ (n : ℕ) (a : Fin N → Fin n → ℝ),
        CentrallySymmetric (permutohull q a) (sampleMean a)) ↔
    ∃ lam : Fin (Nhat N) → ℝ,
      (∀ j, 0 ≤ lam j) ∧
      ∑ j, lam j = 1 ∧
      ∀ X, μ X = ∑ j, lam j * muQ (qbar j) X := by sorry

end RiskUncSets.Symmetric
