-- Prove2me | Theorems.Thm_SphereSOS_DPS_theorem_15
-- name    : SphereSOS.DPS.theorem_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:18:39.385979+00:00
-- url     : https://prove2.me/theorems/3afd0316-b0b8-469f-ba79-e50536141163
-- title:
--   Theorem 15, p. 14 — h_Sep(M) ≤ h_{DPS_ℓ}(M) ≤ (1 + Cd_B²/ℓ²)h_Sep(M) for ℓ ≥ C′d_B, absolute C, C′ > 0
-- statement:
--   There exist absolute constants $C,C'>0$ with the following property. Let $d_A,d_B\ge1$, let $M\in\mathrm{Herm}(d_Ad_B)$, and assume that $(x\otimes y)^\dagger M(x\otimes y)\ge 0$ for all $(x,y)\in\mathbb C^{d_A}\times\mathbb C^{d_B}$. Let $h_{\mathrm{Sep}}(M)=\max\{\mathrm{Tr}[M\rho]:\rho\in\mathrm{Sep}\}$ and $h_{\mathrm{DPS}_\ell}(M)=\max\{\mathrm{Tr}[M\rho]:\rho\in\mathrm{DPS}_\ell\}$, the maxima over trace-one separable states and trace-one elements of the $\ell$-th DPS cone. Then
--   $$h_{\mathrm{Sep}}(M)\le h_{\mathrm{DPS}_\ell}(M)\le\Big(1+\frac{C d_B^2}{\ell^2}\Big)h_{\mathrm{Sep}}(M)\qquad\text{for any }\ell\ge C'd_B.$$
--
--   This recovers the convergence rate $O(d_B^2/\ell^2)$ of the DPS hierarchy of Navascués, Owari and Plenio from the sum-of-squares bound on the sphere.
--
--   **Formalization Note** The level is $\ell=m+1$. The constants are quantified before the dimensions. Sep is $\mathcal{SEP}\cap\{\mathrm{Tr}\rho=1\}$ and the maxima are real suprema; $d_A,d_B\ge1$ (instances `NeZero`) is added so that both sets are nonempty, which the page takes for granted. The hypothesis is the page's $(x\otimes y)^\dagger M(x\otimes y)\ge0$, stated as nonnegativity of the real part.
-- source:
--   Fang, Fawzi, The sum-of-squares hierarchy on the sphere, and applications in quantum information theory, arXiv:1908.05155v1, p. 14, Theorem 15 (= Theorem 4, p. 4, for d_A = d_B = d)

import Mathlib
import Definitions.Def_SphereSOS_DPS_Setting

namespace SphereSOS.DPS

open scoped ComplexOrder

/-- Theorem 15 (p. 14), with ℓ = m + 1: there are absolute constants C, C' > 0 such that for
M ∈ Herm(d_A d_B) with (x ⊗ y)† M (x ⊗ y) ≥ 0 for all (x, y), and ℓ ≥ C' d_B,
h_Sep(M) ≤ h_{DPS_ℓ}(M) ≤ (1 + C d_B² / ℓ²) h_Sep(M). -/
theorem theorem_15 :
    ∃ C C' : ℝ, 0 < C ∧ 0 < C' ∧
      ∀ (dA dB m : ℕ) [NeZero dA] [NeZero dB]
        (M : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ),
        M.IsHermitian →
        (∀ (x : Fin dA → ℂ) (y : Fin dB → ℂ),
          0 ≤ (qf (fun p : Fin dA × Fin dB => x p.1 * y p.2) M).re) →
        C' * (dB : ℝ) ≤ ((m + 1 : ℕ) : ℝ) →
        hSep M ≤ hDPS m M ∧
          hDPS m M ≤ (1 + C * (dB : ℝ) ^ 2 / ((m + 1 : ℕ) : ℝ) ^ 2) * hSep M := by sorry

end SphereSOS.DPS
