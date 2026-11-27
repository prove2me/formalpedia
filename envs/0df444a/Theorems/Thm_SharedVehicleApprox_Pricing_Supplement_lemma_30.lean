-- Prove2me | Theorems.Thm_SharedVehicleApprox_Pricing_Supplement_lemma_30
-- name    : SharedVehicleApprox.Pricing.Supplement.lemma_30
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T18:39:11.668132+00:00
-- url     : https://prove2.me/theorems/e89db9c8-88a5-4cdd-b8af-eec0da6f8162
-- title:
--   Lemma 30, p. 39 — infinite-unit value of redirection without prices (corrected: strongly connected routing; sign condition)
-- statement:
--   Let $n\ge1$, let $\varphi_{ij}\ge0$, and let the per-ride rewards $I_{ij}$ and redirection costs $c_{ij}$ be constants. Let $(\tilde q,\tilde z)$ be an optimum of Algorithm 8 and $\tilde r_{ij}=\tilde z_{ij}/\sum_k\varphi_{ki}\tilde q_k$. Let $\bar\varphi_{ij}=\varphi_{ij}(1-\sum_k\tilde r_{jk})+\sum_k\varphi_{ik}\tilde r_{kj}$ be the demand induced by $\tilde r$ when every customer is served. Assume that $\bar\varphi$ has strongly connected support or $\tilde q=0$, and that $\tilde q\ne0$ or every origin has $\sum_j\varphi_{ij}I_{ij}\ge0$. Then, for every positive solution $\rho$ of the traffic equations of $\bar\varphi$,
--
--   $$\mathrm{Obj}_\infty(\tilde r)=\sum_i\frac{\rho_i}{\rho_{\max}}\sum_j\varphi_{ij}\Bigl(I_{ij}-\sum_k\tilde r_{jk}c_{jk}\Bigr)\ \ge\ \widehat{\mathrm{Obj}}(\tilde q,\tilde r)=\sum_{i,j}(\varphi_{ij}\tilde q_iI_{ij}-c_{ij}\tilde z_{ij}).$$
--
--   The lemma takes the place of Lemma 21 in the proof of Theorem 31: without prices, availabilities do the thinning that quantiles would do.
--
--   Differences from the source:
--   - correction: no connectivity hypothesis → the routing φ̄ of r̃ (all quantiles 1) is strongly connected, or q̃ = 0; reason: false without it: n = 2, φ_12 = φ_21 = 1, I = 1, c = 0, q̃ = (1, 1), z̃_12 = z̃_21 = 1 gives φ̄ = identity; ρ = (1, 2) gives 3/2 < 2. Excluded: q̃ ≠ 0 with reducible routing of r̃
--   - correction: any constant per-ride rewards → q̃ ≠ 0, or Σ_j φ_ij I_ij ≥ 0 at every origin; reason: false without it: n = 1, φ = 1, I = −1, c = 0 gives q̃ = 0 and Obj_∞(r̃) = −1 < 0. Without prices no policy can refuse service, whereas the relaxation can choose q = 0. Excluded: instances with q̃ = 0 and a negative total reward rate Σ_j φ_ij I_ij at some origin. The repair only requires nonnegative total reward rate at each origin, not nonnegative individual ride rewards; when q̃ = 0 feasibility forces z̃ = 0 and the implemented policy has no redirection costs.
--   - reading: Algorithm 8 lists no sign constraint on z → z_ij ≥ 0; reason: z are rates (§5.1), and a negative z would give negative probabilities
--   - reading: a cost c_ij, with no sign stated → any real c_ij; reason: the reading covers every cost matrix, so it is not a weaker one
--   - encoding: the output of Algorithm 8 → any optimal solution of its relaxation; reason: the algorithm returns an optimum; the statement holds for each one and does not need existence
--   - encoding: Obj_∞(r̃) → Σ_i (ρ_i/ρ_max) B_i with B_i = Σ_j φ_ij (I_ij − Σ_k r̃_jk c_jk), for any positive traffic solution ρ; reason: Proposition 6 and the charging argument in the proof of Theorem 22, with all quantiles 1
-- source:
--   Banerjee, Freund & Lykouris, Pricing and Optimization in Shared Vehicle Systems: An Approximation Framework, arXiv:1608.06819v4, p. 39 (PDF 40), Lemma 30; Algorithm 8, p. 39 (PDF 40)

import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson
import Definitions.Def_SharedVehicleApprox_Pricing_Model
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_SupplyRedirection
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_Algorithm3
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_NoPricing

open Finset QueueingFundamentals.Networks

namespace SharedVehicleApprox.Pricing.Supplement

/-- Lemma 30, p. 39 (corrected: the routing of `r̃` is strongly connected unless `q̃ = 0`, and
`q̃ ≠ 0` unless the total reward rate at each origin is nonnegative): the infinite-unit objective of the redirection policy
`r̃` of Algorithm 8, with every customer served when a unit is available, is at least the relaxation
value `Ôbj(q̃, r̃)`. -/
theorem lemma_30 {n : ℕ} [NeZero n] (φ : Fin n → Fin n → ℝ) (hφ : ∀ i j, 0 ≤ φ i j)
    (I c : Fin n → Fin n → ℝ) (qt : Fin n → ℝ) (zt rt : Fin n → Fin n → ℝ)
    (hopt : IsAlg8Optimal φ I c qt zt) (hrt : rt = noPriceRedirectProb φ qt zt)
    (hconn : SupportConnected (inducedDemand φ (fun _ _ => 1) rt) (fun _ _ => 1) ∨ qt = 0)
    (hsign : qt ≠ 0 ∨ ∀ i, 0 ≤ ∑ j, φ i j * I i j)
    (ρ : Fin n → ℝ) (hρ : ∀ i, 0 < ρ i)
    (htr : IsTraffic (inducedDemand φ (fun _ _ => 1) rt) (fun _ _ => 1) ρ) :
    alg8Obj φ I c qt zt ≤ noPriceObjInf φ I c rt ρ := by sorry

end SharedVehicleApprox.Pricing.Supplement
