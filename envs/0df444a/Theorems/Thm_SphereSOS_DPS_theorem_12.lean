-- Prove2me | Theorems.Thm_SphereSOS_DPS_theorem_12
-- name    : SphereSOS.DPS.theorem_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:18:31.544509+00:00
-- url     : https://prove2.me/theorems/b7363673-6cf9-4102-b907-f4137e4082f2
-- title:
--   Theorem 12, p. 12 — SEP* = {p_M ≥ 0}, DPS_ℓ* = {‖y‖^{2(ℓ−1)}p_M rsos}, EXT_ℓ* = {‖y‖^{2(ℓ−1)}p_M csos}
-- statement:
--   Let $\mathcal H_A\simeq\mathbb C^{d_A}$, $\mathcal H_B\simeq\mathbb C^{d_B}$, let $\ell\ge1$ be an integer, and for $M\in\mathrm{Herm}(d_Ad_B)$ let
--   $$p_M(x,\bar x,y,\bar y)=\sum_{ijkl}M_{ij,kl}\,x_i\bar x_k\,y_j\bar y_l\qquad(x\in\mathbb C^{d_A},\ y\in\mathbb C^{d_B})$$
--   be the associated Hermitian polynomial (25). Dual cones are taken inside $\mathrm{Herm}(d_Ad_B)$ with respect to $\langle M,\rho\rangle=\mathrm{Tr}[M\rho]$. Then
--
--   1. $\mathcal{SEP}^*=\{M\in\mathrm{Herm}(d_Ad_B): p_M \text{ is nonnegative}\}$;
--   2. $\mathcal{DPS}_\ell^*=\{M\in\mathrm{Herm}(d_Ad_B):\ \|y\|^{2(\ell-1)}p_M \text{ is rsos}\}$;
--   3. $\mathcal{EXT}_\ell^*=\{M\in\mathrm{Herm}(d_Ad_B):\ \|y\|^{2(\ell-1)}p_M \text{ is csos}\}$.
--
--   Here $\mathcal{SEP}$ is the cone of separable states (18), $\mathcal{DPS}_\ell$ the $\ell$-th level of the Doherty–Parrilo–Spedalieri hierarchy (23) (PSD extensions on $\ell$ copies of $B$ with symmetry and all partial-transpose conditions), $\mathcal{EXT}_\ell$ the same hierarchy without the partial-transpose conditions (24), "rsos" means a sum of squares of Hermitian polynomials, and "csos" a sum of moduli squared of holomorphic polynomials (Definition 11).
--
--   The theorem states precisely that the DPS hierarchy for entanglement detection is, on the dual side, the sum-of-squares hierarchy for nonnegativity of biquadratic Hermitian forms, with multiplier $\|y\|^{2(\ell-1)}$.
--
--   **Formalization Note** The level is $\ell=m+1$, so $\|y\|^{2(\ell-1)}=\|y\|^{2m}$. "$p_M$ nonnegative" is $\operatorname{Re}p_M\ge0$ for all $(x,y)$ ($p_M$ is real for Hermitian $M$). rsos is encoded as a finite sum of squares of real polynomials in the real and imaginary parts of $(x,y)$, which the page notes is equivalent to Definition 11.
-- source:
--   Fang, Fawzi, The sum-of-squares hierarchy on the sphere, and applications in quantum information theory, arXiv:1908.05155v1, p. 12, Theorem 12 (i)–(iii) (first stated as Theorem 3, p. 4); proof p. 13 and Appendix B, pp. 16–20

import Mathlib
import Definitions.Def_SphereSOS_DPS_Setting

namespace SphereSOS.DPS

open scoped ComplexOrder

/-- Theorem 12 (Fang–Fawzi, arXiv:1908.05155v1, p. 12), with ℓ = m + 1:
i) SEP* = {M ∈ Herm : p_M ≥ 0}; ii) DPS_ℓ* = {M ∈ Herm : ‖y‖^{2(ℓ−1)} p_M is rsos};
iii) EXT_ℓ* = {M ∈ Herm : ‖y‖^{2(ℓ−1)} p_M is csos}. -/
theorem theorem_12 (dA dB m : ℕ) :
    dualCone (SEPcone dA dB) = {M | M.IsHermitian ∧ ∀ x y, 0 ≤ (pM M x y).re} ∧
    dualCone (DPScone dA dB m) =
      {M | M.IsHermitian ∧ IsRSOS (fun x y => nsq y ^ m * pM M x y)} ∧
    dualCone (EXTcone dA dB m) =
      {M | M.IsHermitian ∧ IsCSOS (fun x y => nsq y ^ m * pM M x y)} := by sorry

end SphereSOS.DPS
