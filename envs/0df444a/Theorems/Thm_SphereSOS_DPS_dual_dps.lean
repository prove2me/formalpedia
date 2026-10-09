-- Prove2me | Theorems.Thm_SphereSOS_DPS_dual_dps
-- name    : SphereSOS.DPS.dual_dps
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:18:24.379959+00:00
-- url     : https://prove2.me/theorems/4f05d8d2-ff17-4ae7-a618-e65ec1e08bf5
-- title:
--   Appendix B, p. 17 — DPS_ℓ* = {M : M ⊗ I_{B[2:ℓ]} = (Y − Π_ℓYΠ_ℓ) + Σ_{s=0}^ℓ W_s^{T_{B[s]}}, Y Hermitian, W_s ⪰ 0}
-- statement:
--   Let $\ell\ge1$. The dual cone of $\mathcal{DPS}_\ell(\mathcal H_A\otimes\mathcal H_B)$ in $\mathrm{Herm}(d_Ad_B)$ is described by the dual of its semidefinite programming definition (23):
--   $$\mathcal{DPS}_\ell^*=\Big\{M_{AB_1}:\ M_{AB_1}\otimes I_{B[2:\ell]}=\big(Y_{AB[\ell]}-\Pi_\ell Y_{AB[\ell]}\Pi_\ell\big)+\sum_{s=0}^{\ell}W_{s,AB[\ell]}^{\mathsf T_{B[s]}},\ \ Y_{AB[\ell]}\in\mathrm{Herm},\ W_{s,AB[\ell]}\succeq0\ \forall s\in[0:\ell]\Big\}.$$
--   Here $M_{AB_1}\otimes I_{B[2:\ell]}$ acts as $M$ on $A$ and $B_1$ and as the identity on $B_2,\dots,B_\ell$, $\Pi_\ell$ (acting as $I\otimes\Pi_\ell$) is the projector onto the symmetric subspace, and $W^{\mathsf T_{B[s]}}$ is the partial transpose on $B_1,\dots,B_s$. The variable $W_0$ is dual to the positivity of the extension and $W_1,\dots,W_\ell$ to the partial-transpose constraints (22); $Y$ is dual to the symmetry constraint (21).
--
--   Together with Lemma 19 and (39) this gives Theorem 12 (ii).
--
--   **Formalization Note** The level is $\ell=m+1$. The set on the right also requires $M$ Hermitian, since the dual cone lives in $\mathrm{Herm}(d_Ad_B)$; the page's $\Pi_\ell Y\Pi_\ell$ is $(I\otimes\Pi_\ell)Y(I\otimes\Pi_\ell)$ as in (38).
-- source:
--   Fang, Fawzi, The sum-of-squares hierarchy on the sphere, and applications in quantum information theory, arXiv:1908.05155v1, p. 17, Appendix B, display after "First, we can dualize the semidefinite programming definition of DPS_ℓ"

import Mathlib
import Definitions.Def_SphereSOS_DPS_Setting

namespace SphereSOS.DPS

open scoped ComplexOrder

/-- The dual SDP description of DPS_ℓ* (p. 17), with ℓ = m + 1:
DPS_ℓ* = {M : M ⊗ I_{B[2:ℓ]} = (Y − Π_ℓ Y Π_ℓ) + ∑_{s=0}^{ℓ} W_s^{T_{B[s]}}, Y ∈ Herm, W_s ⪰ 0}. -/
theorem dual_dps (dA dB m : ℕ) :
    dualCone (DPScone dA dB m) =
      {M | M.IsHermitian ∧
        ∃ (Y : Matrix (Fin dA × (Fin (m + 1) → Fin dB)) (Fin dA × (Fin (m + 1) → Fin dB)) ℂ) (W : Fin (m + 2) → Matrix (Fin dA × (Fin (m + 1) → Fin dB)) (Fin dA × (Fin (m + 1) → Fin dB)) ℂ),
          Y.IsHermitian ∧ (∀ s, (W s).PosSemidef) ∧
          liftM M = (Y - symProj (m + 1) * Y * symProj (m + 1)) +
            ∑ s : Fin (m + 2), ptB (s : ℕ) (W s)} := by sorry

end SphereSOS.DPS
