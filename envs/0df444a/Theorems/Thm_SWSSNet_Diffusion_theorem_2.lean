-- Prove2me | Theorems.Thm_SWSSNet_Diffusion_theorem_2
-- name    : SWSSNet.Diffusion.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:41:59.527499+00:00
-- url     : https://prove2.me/theorems/8fc4290a-56a6-42a9-9769-7d76e12a1f9c
-- title:
--   Theorem 2 — the SWSS ϑ_p equals (Σ_j d(i,j)θ_j − Σ_ℓ d(i,ℓ)λ̂_ℓ)/Σ_ℓ d(i,ℓ)p_ℓ for every class i
-- statement:
--   Let $p$ be a positive probability vector on the classes and let $d$ be the gains (13) of the tree. For every class $i$, the linear program (LP′) has the optimal value
--   $$
--   \vartheta_p=\frac{\sum_{j}d(i,j)\,\theta_j-\sum_{\ell}d(i,\ell)\,\hat\lambda_\ell}{\sum_{\ell}d(i,\ell)\,p_\ell}, \qquad (14)
--   $$
--   and this value is attained, i.e. it is the largest feasible value of $\vartheta$.
--
--   The theorem computes the SWSS parameter in closed form from the network data. In particular, the same expression results for every choice of the reference class $i$.
--
--   **Formalization Note** The conclusion is `IsGreatest` of the set of feasible values of (LP′): the value (14) is feasible and bounds every feasible value. Hence the supremum defining $\vartheta_p$ is attained and equals (14).
-- source:
--   Hmedi, Arapostathis & Pang, On System-Wide Safety Staffing of Large-Scale Parallel Server Networks, arXiv:2009.01942v3, p. 10, Theorem 2, (14)

import Mathlib
import Definitions.Def_SWSSNet_Diffusion_Network

open Matrix MeasureTheory
open scoped NNReal ENNReal BigOperators

namespace SWSSNet.Diffusion

/-- Theorem 2, p. 10: for every class `i`, the value `ϑ_p` of (LP′) is attained and equals
`(∑_j d(i,j) θ_j − ∑_ℓ d(i,ℓ) λ̂_ℓ) / ∑_ℓ d(i,ℓ) p_ℓ` (14). -/
theorem theorem_2 {I J : ℕ} (N : TreeNetwork I J) (p : Fin I → ℝ) (hp : IsPosProb p) (i : Fin I) :
    IsGreatest {ϑ | lpFeasible N p ϑ}
      ((∑ j, gain N (Sum.inl i) (Sum.inr j) * theta N j
          - ∑ ℓ, gain N (Sum.inl i) (Sum.inl ℓ) * N.lamHat ℓ) /
        ∑ ℓ, gain N (Sum.inl i) (Sum.inl ℓ) * p ℓ) := by sorry

end SWSSNet.Diffusion
