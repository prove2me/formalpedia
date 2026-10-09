-- Prove2me | Theorems.Thm_SphereSOS_DPS_theorem_12_i
-- name    : SphereSOS.DPS.theorem_12_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:18:32.669808+00:00
-- url     : https://prove2.me/theorems/65129676-fe7d-4ffb-9024-47bff1479563
-- title:
--   Theorem 12 (i), p. 12 — SEP* = {M ∈ Herm(d_Ad_B) : p_M is nonnegative}
-- statement:
--   Let $\mathcal{SEP}\subset\mathrm{Herm}(d_Ad_B)$ be the cone of separable (unnormalized) bipartite states on $\mathbb C^{d_A}\otimes\mathbb C^{d_B}$, the finite conic combinations of $(xx^\dagger)\otimes(yy^\dagger)$. For a Hermitian $M$ let $p_M(x,\bar x,y,\bar y)=\sum_{ijkl}M_{ij,kl}x_i\bar x_ky_j\bar y_l$. Then the dual cone of $\mathcal{SEP}$ inside $\mathrm{Herm}(d_Ad_B)$, with respect to the pairing $\langle M,\rho\rangle=\mathrm{Tr}[M\rho]$, is
--   $$\mathcal{SEP}^*=\{M\in\mathrm{Herm}(d_Ad_B):\ p_M(x,\bar x,y,\bar y)\ge 0\ \text{ for all } x\in\mathbb C^{d_A},\ y\in\mathbb C^{d_B}\}.$$
--
--   This is the first part of the duality Theorem 12: witnesses of entanglement are exactly the Hermitian matrices whose biquadratic form is nonnegative.
--
--   **Formalization Note** For Hermitian $M$ the value $p_M(x,\bar x,y,\bar y)$ is real; nonnegativity is stated as $0\le\operatorname{Re}p_M$.
-- source:
--   Fang, Fawzi, The sum-of-squares hierarchy on the sphere, and applications in quantum information theory, arXiv:1908.05155v1, p. 12, Theorem 12 (i)

import Mathlib
import Definitions.Def_SphereSOS_DPS_Setting

namespace SphereSOS.DPS

open scoped ComplexOrder

/-- Theorem 12 (i) (p. 12): SEP* = {M ∈ Herm(d_A d_B) : p_M is nonnegative}. -/
theorem theorem_12_i (dA dB : ℕ) :
    dualCone (SEPcone dA dB) = {M | M.IsHermitian ∧ ∀ x y, 0 ≤ (pM M x y).re} := by sorry

end SphereSOS.DPS
