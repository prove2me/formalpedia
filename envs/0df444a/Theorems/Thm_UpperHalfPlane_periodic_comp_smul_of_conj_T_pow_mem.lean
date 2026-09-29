-- Prove2me | Theorems.Thm_UpperHalfPlane_periodic_comp_smul_of_conj_T_pow_mem
-- name    : UpperHalfPlane.periodic_comp_smul_of_conj_T_pow_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/9e27ad14-d5dc-56c9-8fbb-c5967ec86dcc
-- title:
--   Periodicity of F∘σ when σ T^hσ⁻¹∈Γ
-- statement:
--   Let $\Gamma$ be a subgroup of $\mathrm{SL}_2(\mathbb{Z})$ and let $F:\mathbb{H}\to\mathbb{C}$ be a function on the upper half-plane which is $\Gamma$-invariant in the sense that $F(\gamma\cdot\tau)=F(\tau)$ for every $\gamma\in\Gamma$ and every $\tau\in\mathbb{H}$, the action being the Möbius action of $\mathrm{SL}_2(\mathbb{Z})$ on $\mathbb{H}$. Let $\sigma\in\mathrm{SL}_2(\mathbb{Z})$ and let $h$ be a natural number such that the conjugate $\sigma T^h\sigma^{-1}$ lies in $\Gamma$, where $T=\begin{pmatrix}1&1\\0&1\end{pmatrix}$ is `ModularGroup.T`. Then the function $\mathbb{C}\to\mathbb{C}$ given by $z\mapsto F(\sigma\cdot\mathrm{ofComplex}(z))$ is periodic with period $h$, i.e. its values at $z+h$ and at $z$ agree for every complex $z$. Here `UpperHalfPlane.ofComplex` is the retraction $\mathbb{C}\to\mathbb{H}$ sending $z$ with $\mathrm{Im}\,z>0$ to the corresponding point of $\mathbb{H}$ and every $z$ with $\mathrm{Im}\,z\le 0$ to one fixed point; thus the assertion is periodicity on all of $\mathbb{C}$, not merely on the upper half-plane. No holomorphy, continuity or growth hypothesis on $F$ is imposed, and $h=0$ is permitted.
--
--   This is the standard observation that a $\Gamma$-invariant function on $\mathbb{H}$, transported by $\sigma$, is periodic with any period $h$ for which $\sigma T^h\sigma^{-1}\in\Gamma$ — the numerical input behind the width of the cusp $\sigma\cdot\infty$. Phrasing the conclusion as `Function.Periodic` on $\mathbb{C}$ makes $F\circ\sigma$ available to the machinery of $q$-expansions in the parameter $q_h=e^{2\pi i z/h}$; it is used in the construction of hyperplane sections with controlled logarithmic sums on the modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_UpperHalfPlane_periodic_comp_smul_of_conj_T_pow_mem.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped UpperHalfPlane MatrixGroups

theorem UpperHalfPlane.periodic_comp_smul_of_conj_T_pow_mem {Γ : Subgroup SL(2, ℤ)} {F : ℍ → ℂ}
    (hF : ∀ γ ∈ Γ, ∀ τ : ℍ, F (γ • τ) = F τ) {σ : SL(2, ℤ)} {h : ℕ}
    (hσ : σ * ModularGroup.T ^ h * σ⁻¹ ∈ Γ) :
    Function.Periodic (fun z : ℂ => F (σ • UpperHalfPlane.ofComplex z)) h := by sorry
