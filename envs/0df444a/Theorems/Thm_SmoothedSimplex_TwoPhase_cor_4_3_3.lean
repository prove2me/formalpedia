-- Prove2me | Theorems.Thm_SmoothedSimplex_TwoPhase_cor_4_3_3
-- name    : SmoothedSimplex.TwoPhase.cor_4_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T14:29:10.463516+00:00
-- url     : https://prove2.me/theorems/d38b8ba0-2693-4d0c-8eda-dbeedff2a667
-- title:
--   Corollary 4.3.3 (yᵢ free)
-- statement:
--   Fix positive right-hand sides $y_i$, independent unit objectives $z,t\in\mathbb R^d$, and independent Gaussian vectors $a_i$ centered at $\bar a_i$ with covariance eigenvalues between $\sigma^2$ and $1/(9d\ln n)$. For $n>d\ge3$ and $\sigma>0$,
--   $$\mathbb E\,|\operatorname{Shadow}_{z,t}(a;y)|\le\mathcal D\!\left(n,d,\frac{\sigma}{(1+\max_i\|\bar a_i\|)(\max_i y_i)/(\min_i y_i)}\right)+1.$$
--   This allows unequal positive right-hand sides and general covariance. **Formalization Note** The covariance bounds are equivalent singular-value bounds on the linear maps generating the Gaussian vectors. Independent $z,t$ is inherited from Definition 3.2.4.
-- source:
--   Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7, Corollary 4.3.3, printed p. 56, PDF p. 56

import Mathlib
import Definitions.Def_SmoothedSimplex_TwoPhase_kappaZero
import Definitions.Def_SmoothedSimplex_TwoPhase_shadowBoundD

namespace SmoothedSimplex.TwoPhase

/-- Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7,
Corollary 4.3.3 (yᵢ free), printed p. 56, PDF p. 56. The source’s unit vectors are required to be independent, as in Definition 3.2.4; covariance bounds are expressed as singular-value bounds on Gaussian square roots. Formalization Note: `[n]` is `Fin n`; all expectations use the specified probability laws. -/
theorem cor_4_3_3 {n d : ℕ} (hd : 3 ≤ d) (hnd : d < n)
    (c : Fin n → Point d) (L : Fin n → Point d →ₗ[ℝ] Point d)
    (y : Fin n → ℝ) (hy : ∀ i, 0 < y i) (z t : Point d)
    (hz : ‖z‖ = 1) (ht : ‖t‖ = 1)
    (hind : LinearIndependent ℝ (fun i : Fin 2 => if i = 0 then z else t))
    (σ : ℝ) (hσ : 0 < σ)
    (hlo : ∀ i v, σ * ‖v‖ ≤ ‖L i v‖)
    (hhi : ∀ i v, ‖L i v‖ ≤
      (1 / (3 * Real.sqrt ((d : ℝ) * Real.log n))) * ‖v‖) :
    MeasureTheory.Integrable
      (fun a => ((shadow a y z t).card : ℝ)) (affineGaussianFamily c L) ∧
    (∫ a, ((shadow a y z t).card : ℝ) ∂(affineGaussianFamily c L)) ≤
      shadowBoundD n d (σ / ((1 + sSup (Set.range (fun i : Fin n => ‖c i‖))) *
        (sSup (Set.range y) / sInf (Set.range y)))) + 1 := by sorry

end SmoothedSimplex.TwoPhase
