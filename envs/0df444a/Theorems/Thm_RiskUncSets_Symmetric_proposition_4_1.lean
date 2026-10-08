-- Prove2me | Theorems.Thm_RiskUncSets_Symmetric_proposition_4_1
-- name    : RiskUncSets.Symmetric.proposition_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T12:28:39.47298+00:00
-- url     : https://prove2.me/theorems/9141fca9-acc7-41b1-942c-d31f3f93d22c
-- title:
--   Proposition 4.1: universal central symmetry of a permutohull
-- statement:
--   Let $N\ge1$ and let $q$ be a nonincreasing probability vector in the restricted simplex $\widehat\Delta^N$. For every dimension $n$ and every data set $\mathcal A=(a_1,\ldots,a_N)$ in $\mathbb R^n$, form its $q$-permutohull $\Pi_q(\mathcal A)$ and sample mean $\widehat a$. Then
--
--   $$
--   \bigl[\Pi_q(\mathcal A)\text{ is centrally symmetric through }\widehat a
--   \text{ for every }n,\mathcal A\bigr]
--   \quad\Longleftrightarrow\quad
--   \exists\sigma\in S_N\;\forall i,\;
--     q_i=\frac{2}{N}-q_{\sigma(i)}.
--   $$
--
--   The proposition identifies exactly which weight vectors give a symmetric uncertainty set independently of the data.
--
--   **Formalization Note** The universal quantifier includes every dimension, including zero, and every collection of $N$ vectors; it is essential to the reverse direction. The permutation acts on zero-based `Fin N` indices. Membership of the center in the permutohull is part of central symmetry.
-- source:
--   Bertsimas & Brown, Constructing uncertainty sets for robust linear optimization, Oper. Res. 57(6) (2009), p. 1490, Proposition 4.1 and equation (9); DOI 10.1287/opre.1080.0646

import Definitions.Def_RiskUncSets_Symmetric_Setting

namespace RiskUncSets.Symmetric

theorem proposition_4_1 {N : ℕ} (hN : 0 < N) (q : Fin N → ℝ)
    (hq : q ∈ restrictedSimplex N) :
    (∀ (n : ℕ) (a : Fin N → Fin n → ℝ),
      CentrallySymmetric (permutohull q a) (sampleMean a)) ↔
    ∃ σ : Equiv.Perm (Fin N), q = fun i => 2 / (N : ℝ) - q (σ i) := by sorry

end RiskUncSets.Symmetric
