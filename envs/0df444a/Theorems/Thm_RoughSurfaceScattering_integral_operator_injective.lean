-- Prove2me | Theorems.Thm_RoughSurfaceScattering_integral_operator_injective
-- name    : RoughSurfaceScattering.integral_operator_injective
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T20:55:55.144808+00:00
-- url     : https://prove2.me/theorems/d26c500a-cbad-40fa-a5f9-4307a6eba27f
-- title:
--   Theorem 4.2: the boundary integral operator $\mathcal M$ is injective
-- statement:
--   Let $f\in BC^{1,1}(\mathbb R)$ (the standing assumption $\Gamma\in BC^{1,1}$ of Section 4), let $h_-<f^-$ and $h_+>f^+$, and let $k_\pm,\mu>0$ satisfy $(\mu-1)(k_+^2-k_-^2\mu)\ge0$ and $k_+^2\ne k_-^2\mu$. Let $\mathcal M$ be the $2\times2$ boundary integral operator of equation (4.3), built from the impedance Green's functions $G^{+(\mathcal I)}_{k_+}(\cdot,\cdot;h_-)$ and $G^{-(\mathcal I)}_{k_-}(\cdot,\cdot;h_+)$. Then $\mathcal M$ is injective on $[BC(\Gamma)]^2$: if $\chi=(\varphi,\psi)$ and $\chi'=(\varphi',\psi')$ lie in $[BC(\Gamma)]^2$ and
--
--   $$\mathcal M\chi=\mathcal M\chi'\quad\text{on }\Gamma,$$
--
--   then $\chi=\chi'$. In particular equation (4.3), $\mathcal M\chi=G$, has at most one solution.
--
--   Together with the Fredholm-type results of Natroshvili, Arens and Chandler-Wilde, injectivity gives the existence part of Theorem 4.3.
--
--   **Formalization Note** The hypersingular entry $T^-_{k_-,h_+}-T^+_{k_+,h_-}$ is written as the integral operator with kernel $\partial_{n'(x)}\partial_{n'(y)}(G^{-(\mathcal I)}_{k_-}-G^{+(\mathcal I)}_{k_+})$, whose singularity is integrable. This is the form in which it acts on bounded continuous densities, the space used in the proof. All normal derivatives in $\mathcal M$ are taken along $n'=-n$, pointing into $D^+$, the orientation for which the jump relations (4.19)–(4.20) used in the proof hold. Injectivity is stated as $\mathcal M\chi=\mathcal M\chi'\Rightarrow\chi=\chi'$, which is the paper's "at most one solution" without appealing to linearity.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, claim c002; Section 4, Theorem 4.2, eq. (4.3), PDF p. 14 (operators: Section 4, p. 13; Green's function: eq. (2.8), p. 7)

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem integral_operator_injective (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f)
    (kp km μ : ℝ) (hpar : ParamCond kp km μ) (hm hp : ℝ) (hhm : hm < finf f) (hhp : fsup f < hp)
    (φ ψ φ' ψ' : ℝ → ℂ) (hφ : IsBCGam φ) (hψ : IsBCGam ψ) (hφ' : IsBCGam φ') (hψ' : IsBCGam ψ')
    (hM : Mop f kp km μ hm hp φ ψ = Mop f kp km μ hm hp φ' ψ') :
    φ = φ' ∧ ψ = ψ' := by sorry

end RoughSurfaceScattering
