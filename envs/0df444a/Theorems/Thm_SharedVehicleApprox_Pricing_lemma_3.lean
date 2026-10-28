-- Prove2me | Theorems.Thm_SharedVehicleApprox_Pricing_lemma_3
-- name    : SharedVehicleApprox.Pricing.lemma_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:27:03.645097+00:00
-- url     : https://prove2.me/theorems/042922a6-2d9a-4eda-9541-3de87fafb80e
-- title:
--   Lemma 3, p. 9 — availability in product-form networks: A_i,m = (Z_{m−1}/Z_m)·r_i when ρ_i(y) = r_i^y
-- statement:
--   Consider a product-form network with $m\ge1$ units, $n$ nodes and functions $\rho_j:\mathbb N\to\mathbb R$, whose law is
--   $$\pi(x)=\frac1{Z_m}\prod_{j=1}^n\rho_j(x_j)\quad(x\in S_{n,m}),\qquad Z_m=\sum_{x\in S_{n,m}}\prod_{j=1}^n\rho_j(x_j),$$
--   and $\pi(x)=0$ off $S_{n,m}$. If node $i$ has $\rho_i(y)=r_i^{\,y}$ for all $y$, then its availability $A_{i,m}=\sum_{x\in S_{n,m}}\pi(x)\mathbf 1\{x_i>0\}$ is
--   $$A_{i,m}=\frac{Z_{m-1}}{Z_m}\,r_i.$$
--
--   With Theorem 2 this expresses the availabilities of a state-independent policy through the Gordon–Newell constants, $A_{i,m}(q)=(G_{m-1}(q)/G_m(q))\,r_i(q)$.
--
--   **Formalization Note** The law is `productForm ρ m` of the reused closed-network module; it divides by $Z_m$, and Lean's $x/0=0$ makes both sides $0$ when $Z_m=0$.
--
--   Differences from the source:
--   - generalization: functions ρ_j : ℕ → ℝ_+ (nonnegative, p. 9) → arbitrary real functions ρ_j, Z_m possibly 0; reason: the identity holds for every real ρ_j (both sides are 0 when Z_m = 0), so it specializes to nonnegative ρ_j
--   - encoding: a product-form network whose stationary distribution is π(x) = Z_m⁻¹ Π_j ρ_j(x_j) → π := productForm ρ m; reason: the lemma uses the network only through this law
--   - encoding: m units, Z_{m−1} → hypothesis 1 ≤ m; reason: S_{n,m−1} and Z_{m−1} are defined only for m ≥ 1 (ℕ subtraction)
-- source:
--   Banerjee, Freund & Lykouris, Pricing and Optimization in Shared Vehicle Systems: An Approximation Framework, arXiv:1608.06819v4, p. 9 (PDF 10), Lemma 3, Eq. (5)

import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson
import Definitions.Def_SharedVehicleApprox_Pricing_Model

open Finset QueueingFundamentals.Networks Filter Topology

namespace SharedVehicleApprox.Pricing

/-- Lemma 3, p. 9: in a product-form network with `m ≥ 1` units and functions `ρ_j`, if
`ρ_i(y) = r_i^y` then the availability of node `i` under the product-form law
`π(x) = Z_m⁻¹ ∏_j ρ_j(x_j)` is `A_i,m = (Z_{m−1}/Z_m) · r_i`. -/
theorem lemma_3 {n m : ℕ} (hm : 1 ≤ m) (ρ : Fin n → ℕ → ℝ) (i : Fin n) (r : ℝ)
    (hρ : ∀ y, ρ i y = r ^ y) :
    availability m (productForm ρ m) i = normConst ρ (m - 1) / normConst ρ m * r := by sorry

end SharedVehicleApprox.Pricing
