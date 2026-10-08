-- Prove2me | Theorems.Thm_SpenglerVertical_DoubleMarginalization_lerner_identity
-- name    : SpenglerVertical.DoubleMarginalization.lerner_identity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:54:07.184907+00:00
-- url     : https://prove2.me/theorems/6970528f-f818-4737-b093-c33d0acfe4a0
-- title:
--   Footnote 6 — at the profit-maximizing price, r = c, e = p/(p − r) = p/(p − c) and p = c(e/(e − 1))
-- statement:
--   Let $D$ be a demand curve, $c$ a constant unit cost, and $p$ a profit-maximizing price at cost $c$, i.e. $(x-c)D(x)\le(p-c)D(p)$ for all $x$. Suppose $D$ is differentiable at $p$ and $D(p)>0$. Write $e=-pD'(p)/D(p)$ for the elasticity of demand at $p$ and $r=p+D(p)/D'(p)$ for the marginal revenue at $p$. Then $D'(p)\ne0$, $p\ne c$, marginal revenue equals marginal cost, $r=c$, and
--   $$e=\frac{p}{p-r}=\frac{p}{p-c},\qquad p=c\,\frac{e}{e-1}\quad(\text{if } c\neq 0).$$
--
--   These are the equilibrium identities of a monopolist (the Lerner relation between markup and elasticity), stated by Spengler in footnote 6 and used throughout Section III to relate the profit-maximizing price to cost and elasticity.
--
--   **Formalization Note** The paper takes the existence of marginal revenue for granted; the Lean statement assumes differentiability of $D$ at $p$ and $D(p)>0$ (positive sales), without which $e$ and $r$ are junk values. The clause $p=c\,e/(e-1)$ needs $c\ne0$: at $c=0$ one has $e=1$ and the fraction is undefined.
-- source:
--   Spengler, Vertical integration and antitrust policy, J. Polit. Econ. 58 (1950), p. 350, footnote 6; https://doi.org/10.1086/256964

import Mathlib
import Definitions.Def_SpenglerVertical_DoubleMarginalization_Model

namespace SpenglerVertical.DoubleMarginalization

theorem lerner_identity (D : ℝ → ℝ) (c p : ℝ)
    (hmax : IsProfitMax D c p) (hdiff : DifferentiableAt ℝ D p) (hQ : 0 < D p) :
    deriv D p ≠ 0 ∧ p ≠ c ∧
    marginalRevenue D p = c ∧
    elasticity D p = p / (p - marginalRevenue D p) ∧
    elasticity D p = p / (p - c) ∧
    (c ≠ 0 → p = c * (elasticity D p / (elasticity D p - 1))) := by sorry

end SpenglerVertical.DoubleMarginalization
