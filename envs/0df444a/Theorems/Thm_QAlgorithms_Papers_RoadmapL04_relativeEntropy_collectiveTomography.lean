-- Prove2me | Theorems.Thm_QAlgorithms_Papers_RoadmapL04_relativeEntropy_collectiveTomography
-- name    : QAlgorithms.Papers.RoadmapL04.relativeEntropy_collectiveTomography
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:22:19.015996+00:00
-- url     : https://prove2.me/theorems/ac19f3fa-bb40-4894-b1a7-6678e33c2e0f
-- title:
--   Collective tomography with relative entropy accuracy
-- statement:
--   There are absolute constants $C>0$ and $0<\epsilon_0\le 1/2$ with the following property. For every integer dimension $d\ge 1$, supplied integer rank bound $1\le r\le d$, and accuracy $0<\epsilon\le\epsilon_0$, one can choose a copy count $n\ge 0$ and a lawful collective measurement on $n$ independent identical copies of a state, with a density matrix as its classical outcome, such that
--
--   $$
--   n\le C\frac{rd}{\epsilon}\left(\ln\frac{d}{\epsilon}\right)^2,\qquad \Pr_{\widehat\rho\sim\mathcal M(\rho^{\otimes n})}\!\left[S(\rho\Vert\widehat\rho)\le\epsilon\right]\ge 0.99.
--   $$
--
--   The probability guarantee holds for every unknown positive semidefinite $d\times d$ matrix $\rho$ of trace one and rank at most $r$. The measurement is chosen using only $d,r,\epsilon$, before $\rho$. Here $S$ is Umegaki quantum relative entropy with natural logarithms: $S(\rho\Vert\sigma)=\operatorname{Tr}(\rho\ln\rho-\rho\ln\sigma)$ when $\operatorname{supp}\rho\subseteq\operatorname{supp}\sigma$, and $+\infty$ otherwise; zero-eigenvalue terms use their continuous limits. The estimate may have any rank.
--
--   This gives relative entropy tomography with $\widetilde O(rd/\epsilon)$ copies, including singular input states. Larger positive accuracies follow by running at a fixed smaller accuracy. The explicit squared-logarithm bound is stated on PDF p.12 immediately after Theorem 2.34.
--
--   **Formalization Note** The measurement uses the frozen general operator-valued POVM on the space of density matrices, and its output distribution is the Born law on $\rho^{\otimes n}$. The extended divergence uses the frozen kernel-containment support guard.
-- source:
--   Quantum chi-squared tomography and mutual information testing, arXiv:2305.18519v2, Corollary 1.8, PDF p. 4. https://arxiv.org/abs/2305.18519v2 . PDF SHA-256: 62f46bb9a749848858da26e0c5933a702a1559c9a8aa48943657f2e1f7d82e42.

import Definitions.Def_QAlgorithms_Defs_TomographyOutcomes
import Definitions.Def_QAlgorithms_Defs_ExtendedQuantumEntropy
set_option autoImplicit false

namespace QAlgorithms.Papers.RoadmapL04

open scoped ENNReal

/-- Corollary 1.8 (arXiv:2305.18519v2, PDF p.4): collective tomography of a
`d`-dimensional density matrix of rank at most the public bound `r`, with Umegaki
relative entropy at most `eps` with probability at least .99. Natural logarithms
and the support-violation value `+infinity` are supplied by `umegakiEntropy`.
The uniform copy bound `O((r*d/eps) * log(d/eps)^2)` is the paper's explicit
counterpart on PDF p.12. The absolute small-error threshold spells out the
asymptotic regime; other positive accuracies follow by using a smaller accuracy.
The collective POVM, whose outcomes are density matrices, is chosen before `rho`.
No positivity of the smallest eigenvalue or rank constraint on the estimate is required. -/
theorem relativeEntropy_collectiveTomography :
    ∃ C : ℝ, 0 < C ∧ ∃ eps0 : ℝ, 0 < eps0 ∧ eps0 ≤ 1 / 2 ∧
      ∀ d : ℕ, 1 ≤ d → ∀ r : ℕ, 1 ≤ r → r ≤ d →
      ∀ eps : ℝ, 0 < eps → eps ≤ eps0 →
      ∃ n : ℕ, ∃ measurement : QAlgorithms.Tomography.CollectiveMeasurement d n,
        (n : ℝ) ≤ C * ((r : ℝ) * (d : ℝ) / eps) * (Real.log ((d : ℝ) / eps)) ^ 2 ∧
        ∀ rho : Matrix (Fin d) (Fin d) ℂ, ∀ density : IsDensityMatrix rho,
          rho.rank ≤ r →
          QAlgorithms.Tomography.collectiveOutcomeLaw measurement rho density
            {sigma | QAlgorithms.QuantumLoss.umegakiEntropy rho sigma.val density sigma.property ≤
              ENNReal.ofReal eps} ≥ ENNReal.ofReal (99 / 100 : ℝ) := by sorry

end QAlgorithms.Papers.RoadmapL04
