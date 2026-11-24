-- Prove2me | Theorems.Thm_SongZhangKLS_poincare_L2_universal
-- name    : SongZhangKLS.poincare_L2_universal
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-24T08:34:20.358323+00:00
-- url     : https://prove2.me/theorems/67e9b271-e744-474a-92fe-bbf5168af33d
-- title:
--   Universal Poincaré bound with $L^2$ clause for isotropic log-concave measures
-- statement:
--   This is the Poincaré half of Theorem 6.1 of Song–Zhang, including its $L^2$ clause.
--
--   There is a universal constant $C>0$ with the following property. Let $n\ge0$ and let $\mu$ be an isotropic log-concave probability measure on $\mathbb R^n$ (log-concave in the sense of the Brunn–Minkowski inequality $\mu(tK_0+(1-t)K_1)\ge\mu(K_0)^t\mu(K_1)^{1-t}$ for compact $K_0,K_1$, and isotropic: finite second moment, mean $0$, covariance $I_n$). Then every locally Lipschitz function $f:\mathbb R^n\to\mathbb R$ with finite Dirichlet energy $\int\|\nabla f\|^2\,d\mu<\infty$ belongs to $L^2(\mu)$ and satisfies
--
--   $$
--   \mathrm{Var}_\mu[f]\;\le\;C\int_{\mathbb R^n}\|\nabla f\|^2\,d\mu .
--   $$
--
--   The constant does not depend on $n$, $\mu$ or $f$. In particular $C_P(\mu)\le C$ for the Poincaré constant of eq. (1) of the paper, which includes the requirement that every finite-energy locally Lipschitz function is square integrable.
--
--   **Formalization Note** $\nabla f$ is Mathlib's `gradient` (zero where $f$ is not differentiable); the energy is `dirichletEnergy`, a lower Lebesgue integral in $[0,\infty]$, and the variance is `evariance`. Log-concavity and isotropy are the published `FunctionalInequalities.KLS.LogConcave` and `FunctionalInequalities.KLS.Isotropic`.
-- source:
--   Song, Zhang, An O(1) Bound for the KLS Constant, arXiv:2610.01447 (October 2026), Theorem 6.1, p.63 (Poincaré clause and L^2 clause)

import Mathlib
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_LogConcave
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_Isotropic
import Definitions.Def_SongZhangKLS_poincareConst

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SongZhangKLS
theorem poincare_L2_universal :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))),
      FunctionalInequalities.KLS.LogConcave μ → FunctionalInequalities.KLS.Isotropic μ →
      ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, LocallyLipschitz f →
        dirichletEnergy (μ : Measure (EuclideanSpace ℝ (Fin n))) f < ⊤ →
        MemLp f 2 (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
        evariance f (μ : Measure (EuclideanSpace ℝ (Fin n))) ≤
          ENNReal.ofReal C * dirichletEnergy (μ : Measure (EuclideanSpace ℝ (Fin n))) f := by sorry
end SongZhangKLS
