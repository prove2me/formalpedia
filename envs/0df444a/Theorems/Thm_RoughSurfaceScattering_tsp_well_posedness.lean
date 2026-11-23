-- Prove2me | Theorems.Thm_RoughSurfaceScattering_tsp_well_posedness
-- name    : RoughSurfaceScattering.tsp_well_posedness
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T20:56:32.821866+00:00
-- url     : https://prove2.me/theorems/5ac2dcc9-6bd8-4af8-b25c-62a09d16ce01
-- title:
--   Theorem 4.3: well-posedness of the transmission scattering problem
-- statement:
--   Let $f\in BC^{1,1}(\mathbb R)$, let $k_\pm,\mu>0$ satisfy $(\mu-1)(k_+^2-k_-^2\mu)\ge0$ and $k_+^2\ne k_-^2\mu$, let $\alpha\in(0,1)$, and let $h_-,h_+\in\mathbb R$ with
--
--   $$h_-<f^-<f^+<h_+.$$
--
--   1. For every $g_1\in BC^{1,\alpha}(\Gamma)$ and $g_2\in BC^{0,\alpha}(\Gamma)$ the TSP has exactly one solution $(u_+,u_-)$. There is $\chi=(\varphi,\psi)\in BC^{1,\alpha}(\Gamma)\times BC^{0,\alpha}(\Gamma)$ with $\mathcal M\chi=G=(g_1,g_2)$, it is the only solution of (4.14) in $[BC(\Gamma)]^2$, and the solution is
--   $$u_+=\mathcal D^+_{k_+,h_-}\varphi+\mathcal S^+_{k_+,h_-}\psi\ \text{in }D^+,\qquad u_-=\mu^{-1}\big(\mathcal D^-_{k_-,h_+}\varphi+\mathcal S^-_{k_-,h_+}\psi\big)\ \text{in }D^-,$$
--   with $u_\pm\in C^2(D^\pm)\cap C^1(\overline{D^\pm})\cap BC^1(\overline{D^\pm_{h_\pm}})$.
--   2. $\mathcal M$ maps $[BC(\Gamma)]^2$ into itself bijectively, with bounded inverse: $\|\varphi\|_{\infty,\Gamma}+\|\psi\|_{\infty,\Gamma}\le C\,\|\mathcal M\chi\|_{\infty}$.
--   3. In the strips $D^\pm_{h_\pm}$ between $\Gamma$ and $\Gamma_{h_\pm}$, $|u_\pm|\le C(\|g_1\|_{\infty,\Gamma}+\|g_2\|_{\infty,\Gamma})$ and $|\nabla u_\pm|\le C(\|g_1\|_{1,\alpha,\Gamma}+\|g_2\|_{0,\alpha,\Gamma})$, with $C$ independent of the data.
--
--   This is the paper's main result on the direct problem.
--
--   **Formalization Note** "Depend continuously on" the norms of the data is stated as the linear bounds in item 3, with constants independent of $(g_1,g_2)$, and $|\nabla u|$ is the operator norm of the derivative. The strict inequality $f^-<f^+$ of the printed hypothesis is kept. "Bijective in $[BC(\Gamma)]^2$" is stated as: $\mathcal M$ maps $[BC(\Gamma)]^2$ to itself, and each $G\in[BC(\Gamma)]^2$ has exactly one preimage there. $C^1(\overline{D^\pm})$ and $BC^1(\overline{D^\pm_{h_\pm}})$ refer to the same continuous gradient field. The potentials and $\mathcal M$ use the upward normal $n'=-n$ and the TSP uses $n$; with this convention the ansatz reduces the TSP exactly to $\mathcal M\chi=(g_1,g_2)$ (with $n$ in the potentials as well, the reduction would give a different matrix and the statement would be false).
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, claim c009; Section 4, Theorem 4.3, eq. (4.14), PDF p. 16

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem tsp_well_posedness (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f)
    (kp km μ : ℝ) (hpar : ParamCond kp km μ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (hm hp : ℝ) (hh : hm < finf f ∧ finf f < fsup f ∧ fsup f < hp) :
    (∀ g1 g2 : ℝ → ℂ, IsBC1AlphaGam f α g1 → IsBC0AlphaGam f α g2 →
      (∃! u : (R2 → ℂ) × (R2 → ℂ), IsTSPSolution f kp km μ g1 g2 u.1 u.2) ∧
      ∃ φ ψ : ℝ → ℂ, IsBC1AlphaGam f α φ ∧ IsBC0AlphaGam f α ψ ∧
        Mop f kp km μ hm hp φ ψ = (g1, g2) ∧
        (∀ φ' ψ' : ℝ → ℂ, IsBCGam φ' → IsBCGam ψ' →
          Mop f kp km μ hm hp φ' ψ' = (g1, g2) → φ' = φ ∧ ψ' = ψ) ∧
        ∀ u : (R2 → ℂ) × (R2 → ℂ), IsTSPSolution f kp km μ g1 g2 u.1 u.2 →
          (∀ x ∈ Dplus f, u.1 x = doubleLayer f kp hm 1 φ x + singleLayer f kp hm 1 ψ x) ∧
          (∀ x ∈ Dminus f, u.2 x =
            (μ : ℂ)⁻¹ * (doubleLayer f km hp (-1) φ x + singleLayer f km hp (-1) ψ x)) ∧
          ContDiffOn ℝ 2 u.1 (Dplus f) ∧ ContDiffOn ℝ 2 u.2 (Dminus f) ∧
          (∃ Dp : R2 → (R2 →L[ℝ] ℂ),
            IsC1On (closure (Dplus f)) u.1 Dp ∧ IsBC1On (stripPlus f hp) u.1 Dp) ∧
          (∃ Dm : R2 → (R2 →L[ℝ] ℂ),
            IsC1On (closure (Dminus f)) u.2 Dm ∧ IsBC1On (stripMinus f hm) u.2 Dm)) ∧
    (∀ φ ψ : ℝ → ℂ, IsBCGam φ → IsBCGam ψ →
      IsBCGam (Mop f kp km μ hm hp φ ψ).1 ∧ IsBCGam (Mop f kp km μ hm hp φ ψ).2) ∧
    (∀ G1 G2 : ℝ → ℂ, IsBCGam G1 → IsBCGam G2 →
      ∃! χ : (ℝ → ℂ) × (ℝ → ℂ), IsBCGam χ.1 ∧ IsBCGam χ.2 ∧
        Mop f kp km μ hm hp χ.1 χ.2 = (G1, G2)) ∧
    (∃ C : ℝ, ∀ φ ψ : ℝ → ℂ, IsBCGam φ → IsBCGam ψ →
      supNormGam φ + supNormGam ψ ≤
        C * (supNormGam (Mop f kp km μ hm hp φ ψ).1 + supNormGam (Mop f kp km μ hm hp φ ψ).2)) ∧
    (∃ C : ℝ, ∀ g1 g2 : ℝ → ℂ, IsBC1AlphaGam f α g1 → IsBC0AlphaGam f α g2 →
      ∀ u : (R2 → ℂ) × (R2 → ℂ), IsTSPSolution f kp km μ g1 g2 u.1 u.2 →
        (∀ x ∈ Dplus f ∩ Uminus hp, ‖u.1 x‖ ≤ C * (supNormGam g1 + supNormGam g2)) ∧
        ∀ x ∈ Dminus f ∩ Uplus hm, ‖u.2 x‖ ≤ C * (supNormGam g1 + supNormGam g2)) ∧
    (∃ C : ℝ, ∀ g1 g2 : ℝ → ℂ, IsBC1AlphaGam f α g1 → IsBC0AlphaGam f α g2 →
      ∀ u : (R2 → ℂ) × (R2 → ℂ), IsTSPSolution f kp km μ g1 g2 u.1 u.2 →
        (∀ x ∈ Dplus f ∩ Uminus hp,
          ‖fderiv ℝ u.1 x‖ ≤ C * (holderNorm1 f α g1 + holderNorm0 f α g2)) ∧
        ∀ x ∈ Dminus f ∩ Uplus hm,
          ‖fderiv ℝ u.2 x‖ ≤ C * (holderNorm1 f α g1 + holderNorm0 f α g2)) := by sorry

end RoughSurfaceScattering
