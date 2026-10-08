-- Prove2me | Theorems.Thm_PoissonDirichlet_ChainLimit_eq_37
-- name    : PoissonDirichlet.ChainLimit.eq_37
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:35:45.201985+00:00
-- url     : https://prove2.me/theorems/7ee75c95-cbb2-4146-be5b-eb879538f02c
-- title:
--   Proposition 11 (ii), (37): the convolution law and Laplace transform of Σ_n
-- statement:
--   Let $0<\alpha<1$ and let $(V_n)$ have the $\mathrm{PD}(\alpha,0)$ distribution. For each $n\ge1$, put $\Sigma_n=(V_{n+1}+V_{n+2}+\cdots)/V_n$. Then $\Sigma_n$ has the law of the sum of $n$ independent copies of $\Sigma_1$, and for every $\lambda\ge0$,
--   $$\mathbb E_{\alpha,0}[e^{-\lambda\Sigma_n}]=\psi_\alpha(\lambda)^{-n}.$$
--   The convolution law supplies the one-dimensional distributions used in the asymptotic analysis of $Y_n$.
--
--   **Formalization Note** The paper's $n$ is `k+1` in Lean. The law of $\Sigma_1$ is obtained from its random variable under the same probability measure. At $\lambda=0$, both sides are $1$.
-- source:
--   Pitman and Yor, The two-parameter Poisson–Dirichlet distribution derived from a stable subordinator, Ann. Probab. 25 (1997), pp. 863–864, Proposition 11 (ii), (37)

import Mathlib
import Definitions.Def_PoissonDirichlet_ChainLimit_Setting
open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.ChainLimit

/-- Proposition 11(ii), (37), p. 864. `Σ_{k+1}` has the law of the sum of
`k+1` independent copies of `Σ₁`, and its Laplace transform is `ψ_α(l)^{-(k+1)}`. -/
theorem eq_37 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (V : Ω → ℕ → ℝ) (hV : HasPD α 0 P V) (k : ℕ) :
    HasLaw (fun ω => Sigseq (V ω) k)
      (convPow (P.map fun ω => Sigseq (V ω) 0) (k + 1)) P ∧
    ∀ l : ℝ, 0 ≤ l →
      ∫ ω, Real.exp (-l * Sigseq (V ω) k) ∂P =
        (psi α l ^ (k + 1))⁻¹ := by sorry

end PoissonDirichlet.ChainLimit
