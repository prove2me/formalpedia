-- Prove2me | Theorems.Thm_SteerableE2CNN_localized_nonlinearity_equivariant
-- name    : SteerableE2CNN.localized_nonlinearity_equivariant
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T09:39:21.464129+00:00
-- url     : https://prove2.me/theorems/ea37fbb1-ac0b-41b2-85ee-125d349d1028
-- title:
--   Appendix D.2: equivariant localized nonlinearities are equivariant on fields
-- statement:
--   Let $G\le\mathrm{O}(2)$, let $\rho_{\mathrm{in}},\rho_{\mathrm{out}}$ be representations of $G$ on $\mathbb{R}^{n}$ and $\mathbb{R}^{m}$, and let $\sigma:\mathbb{R}^{n}\to\mathbb{R}^{m}$ satisfy $\sigma\circ\rho_{\mathrm{in}}(g)=\rho_{\mathrm{out}}(g)\circ\sigma$ for all $g\in G$. Let $\bar\sigma(f)(x)=\sigma(f(x))$ be the nonlinearity applied to a whole field. Then for every field $f$, every $t\in\mathbb{R}^2$ and every $g\in G$,
--
--   $$\bar\sigma\big([\operatorname{Ind}\rho_{\mathrm{in}}](tg)f\big)=[\operatorname{Ind}\rho_{\mathrm{out}}](tg)\,\bar\sigma(f).$$
-- source:
--   Weiler and Cesa, General E(2)-Equivariant Steerable CNNs, arXiv:1911.08251v2 (NeurIPS 2019), Section 2.6, p. 6; Appendix D.2 (Equivariance of spatially localized nonlinearities), p. 22

import Mathlib
import Definitions.Def_SteerableE2CNN_Basic

open Matrix MeasureTheory

namespace SteerableE2CNN

theorem localized_nonlinearity_equivariant (G : Subgroup O2)
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (ρin : MatRep G n) (ρout : MatRep G m) (σ : (n → ℝ) → (m → ℝ))
    (hσ : ∀ (g : G) (v : n → ℝ), σ (repMat ρin g *ᵥ v) = repMat ρout g *ᵥ σ v)
    (t : Plane) (g : G) (f : Plane → n → ℝ) :
    (fun x => σ (indAct G ρin t g f x)) = indAct G ρout t g (fun x => σ (f x)) := by sorry

end SteerableE2CNN
