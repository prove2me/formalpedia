-- Prove2me | Theorems.Thm_SteerableE2CNN_norm_nonlinearity_equivariant
-- name    : SteerableE2CNN.norm_nonlinearity_equivariant
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T09:39:49.852743+00:00
-- url     : https://prove2.me/theorems/fb66ce88-0fbf-4393-a448-70bcb10fabcf
-- title:
--   Appendix D.2.2: norm nonlinearities are equivariant under unitary representations
-- statement:
--   Let $G\le\mathrm{O}(2)$ and let $\rho$ be a unitary representation of $G$ on $\mathbb{R}^{n}$, i.e. $|\rho(g)v|=|v|$ for all $g$ and $v$, where $|\cdot|$ is the Euclidean norm. For any function $\eta$, the norm nonlinearity $\sigma_{\mathrm{norm}}(v)=\eta(|v|)\,\dfrac{v}{|v|}$ satisfies
--
--   $$\sigma_{\mathrm{norm}}(\rho(g)v)=\rho(g)\,\sigma_{\mathrm{norm}}(v)\qquad\forall g\in G,\ v\in\mathbb{R}^{n}.$$
--
--   Examples are norm-ReLUs, squashing nonlinearities and gated nonlinearities.
--
--   **Formalization Note** The paper's formula is undefined at $v=0$. In Lean, $v/|v|$ is $0$ there, so $\sigma_{\mathrm{norm}}(0)=0$. The function $\eta$ is taken on all of $\mathbb{R}$; only its values on $[0,\infty)$ enter.
-- source:
--   Weiler and Cesa, General E(2)-Equivariant Steerable CNNs, arXiv:1911.08251v2 (NeurIPS 2019), Section 2.6, p. 6; Appendix D.2.2, p. 23

import Mathlib
import Definitions.Def_SteerableE2CNN_Basic

open Matrix MeasureTheory

namespace SteerableE2CNN

theorem norm_nonlinearity_equivariant (G : Subgroup O2)
    {n : Type*} [Fintype n] [DecidableEq n] (ρ : MatRep G n)
    (hρ : ∀ (g : G) (v : n → ℝ), eNorm (repMat ρ g *ᵥ v) = eNorm v)
    (η : ℝ → ℝ) (g : G) (v : n → ℝ) :
    normNL η (repMat ρ g *ᵥ v) = repMat ρ g *ᵥ normNL η v := by sorry

end SteerableE2CNN
