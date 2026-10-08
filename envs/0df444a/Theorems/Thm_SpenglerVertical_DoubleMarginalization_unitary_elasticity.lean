-- Prove2me | Theorems.Thm_SpenglerVertical_DoubleMarginalization_unitary_elasticity
-- name    : SpenglerVertical.DoubleMarginalization.unitary_elasticity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:54:03.28587+00:00
-- url     : https://prove2.me/theorems/c5b69204-4327-4d67-b4ca-fd416737d77b
-- title:
--   Section III — at zero cost the monopoly price is where demand is unitarily elastic; at positive cost demand is more than unitarily elastic
-- statement:
--   Let $D$ be a non-increasing demand curve, $c$ a constant unit cost and $p$ a profit-maximizing price at cost $c$, with $D$ differentiable at $p$ and $D(p)>0$. Let $e(p)=-pD'(p)/D(p)$ be the elasticity of demand at $p$. Then:
--
--   1. if $c=0$, demand is unitarily elastic at $p$: $e(p)=1$;
--   2. if $c>0$, the price exceeds the cost and demand is more than unitarily elastic:
--   $$c<p\quad\text{and}\quad e(p)>1.$$
--
--   This is the observation of Section III that a monopolist never prices in the inelastic part of the demand curve, and prices strictly in its elastic part once marginal cost is positive.
--
--   **Formalization Note** Differentiability of $D$ at $p$ and $D(p)>0$ are added: the paper reasons with marginal revenue, which presupposes them. The monotonicity of $D$ is used only in the second clause.
-- source:
--   Spengler, Vertical integration and antitrust policy, J. Polit. Econ. 58 (1950), p. 350, Section III; https://doi.org/10.1086/256964

import Mathlib
import Definitions.Def_SpenglerVertical_DoubleMarginalization_Model

namespace SpenglerVertical.DoubleMarginalization

theorem unitary_elasticity (D : ℝ → ℝ) (c p : ℝ) (hD : Antitone D)
    (hmax : IsProfitMax D c p) (hdiff : DifferentiableAt ℝ D p) (hQ : 0 < D p) :
    (c = 0 → elasticity D p = 1) ∧
    (0 < c → c < p ∧ 1 < elasticity D p) := by sorry

end SpenglerVertical.DoubleMarginalization
