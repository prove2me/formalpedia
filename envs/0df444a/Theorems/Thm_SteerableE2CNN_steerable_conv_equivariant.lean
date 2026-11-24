-- Prove2me | Theorems.Thm_SteerableE2CNN_steerable_conv_equivariant
-- name    : SteerableE2CNN.steerable_conv_equivariant
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T09:37:45.669297+00:00
-- url     : https://prove2.me/theorems/20442767-5f8a-4280-84c7-30701a5cbf20
-- title:
--   Appendix D.1: convolution with a $G$-steerable kernel is equivariant
-- statement:
--   Let $G\le\mathrm{O}(2)$, let $\rho_{\mathrm{in}}:G\to\mathrm{GL}(\mathbb{R}^{n})$ and $\rho_{\mathrm{out}}:G\to\mathrm{GL}(\mathbb{R}^{m})$ be representations, and let $k:\mathbb{R}^2\to\mathbb{R}^{m\times n}$ be a $G$-steerable kernel:
--
--   $$k(gx)=\rho_{\mathrm{out}}(g)\,k(x)\,\rho_{\mathrm{in}}(g)^{-1}\qquad\forall g\in G,\ x\in\mathbb{R}^2.$$
--
--   Let $f:\mathbb{R}^2\to\mathbb{R}^{n}$ be a field for which $y\mapsto k(y)f(x+y)$ is Lebesgue integrable for every $x$. Then for every $t\in\mathbb{R}^2$ and $g\in G$ the convolution $(k\star f)(x)=\int k(y)f(x+y)\,dy$ satisfies
--
--   $$k\star\big([\operatorname{Ind}\rho_{\mathrm{in}}](tg)f\big)=[\operatorname{Ind}\rho_{\mathrm{out}}](tg)\,(k\star f),$$
--
--   where $([\operatorname{Ind}\rho](tg)f)(x)=\rho(g)f(g^{-1}(x-t))$.
--
--   The kernel constraint is therefore sufficient for a convolution layer to map $\rho_{\mathrm{in}}$-fields equivariantly to $\rho_{\mathrm{out}}$-fields.
--
--   **Formalization Note** The paper assumes tacitly that the convolution exists. The Lean statement assumes the integrability of $y\mapsto k(y)f(x+y)$ for every $x$.
-- source:
--   Weiler and Cesa, General E(2)-Equivariant Steerable CNNs, arXiv:1911.08251v2 (NeurIPS 2019), Section 2.3, eqs. (1)-(2), pp. 3-4; Appendix D.1 (Equivariance of E(2)-steerable convolutions), p. 21

import Mathlib
import Definitions.Def_SteerableE2CNN_Basic

open Matrix MeasureTheory

namespace SteerableE2CNN

theorem steerable_conv_equivariant (G : Subgroup O2)
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (ρin : MatRep G n) (ρout : MatRep G m) (k : Plane → Matrix m n ℝ)
    (hk : IsSteerable G ρin ρout k) (f : Plane → n → ℝ)
    (hf : ∀ x : Plane, Integrable (fun y : Plane => k y *ᵥ f (x + y))) (t : Plane) (g : G) :
    steerConv k (indAct G ρin t g f) = indAct G ρout t g (steerConv k f) := by sorry

end SteerableE2CNN
