-- Prove2me | Theorems.Thm_SpenglerVertical_DoubleMarginalization_linear_demand_elasticity
-- name    : SpenglerVertical.DoubleMarginalization.linear_demand_elasticity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:54:06.976803+00:00
-- url     : https://prove2.me/theorems/fb1bd718-83af-40c1-bcd4-137e210ab43d
-- title:
--   Footnote 6 — straight-line demand: p* = (a + c)/2, Δr = 2Δp, e = (a + c)/(a − c), and elasticity rises relatively faster than price
-- statement:
--   Let $a>0$, $b>0$ and let $D(p)=b(a-p)$ be a straight-line demand curve. Write $e(p)=-pD'(p)/D(p)$ for its elasticity and $r(p)=p+D(p)/D'(p)$ for its marginal revenue. Then:
--
--   1. for every unit cost $c$, the profit-maximizing prices at cost $c$ are exactly $p^*(c)=\tfrac{a+c}{2}$;
--   2. marginal revenue is $r(p)=2p-a$, so an increment $\Delta p$ in price moves marginal revenue by $\Delta r=2\Delta p$;
--   3. for $c<a$, the elasticity at the profit-maximizing price is
--   $$e\big(p^*(c)\big)=\frac{a+c}{a-c},$$
--   and in particular $e(p^*(0))=e(a/2)=1$;
--   4. for $0\le c<c'<a$, the elasticity rises relatively more than the price:
--   $$\frac{e(p^*(c'))}{e(p^*(c))}>\frac{p^*(c')}{p^*(c)};$$
--   5. the relative rise in elasticity caused by a given increment $\Delta>0$ in cost grows with the level of cost: for $0\le c<c'$ with $c'+\Delta<a$,
--   $$\frac{e(p^*(c'+\Delta))}{e(p^*(c'))}>\frac{e(p^*(c+\Delta))}{e(p^*(c))}.$$
--
--   Footnote 6 illustrates the claim that "an increment in cost is accompanied by a relatively greater increment in the elasticity" on a straight-line demand curve, and adds that the relative rise is "greater still, varying directly with the magnitude of $c$".
--
--   **Formalization Note** Footnote 6 prints, for the case $r=c=0$, $e'=(p+\Delta p)/(p-2\Delta p)$ with the rise in $e$ "approximating $3\Delta p/p$". With $p=a/2$ and $\Delta p=\Delta c/2$, item 3 gives the exact value $e'=(p+\Delta p)/(p-\Delta p)$, whose rise is approximately $2\Delta p/p$; the corrected exact formula is stated and the approximation is not formalized. "Relatively greater increment" is read as item 4 (relative rise in $e$ exceeds the relative rise in the price), the comparison the footnote's own example makes; the literal reading $\Delta e/e>\Delta c/c$ is false for small $c$.
-- source:
--   Spengler, Vertical integration and antitrust policy, J. Polit. Econ. 58 (1950), pp. 350–351, footnote 6; https://doi.org/10.1086/256964

import Mathlib
import Definitions.Def_SpenglerVertical_DoubleMarginalization_Model

namespace SpenglerVertical.DoubleMarginalization

theorem linear_demand_elasticity (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∀ c p : ℝ, IsProfitMax (linearDemand a b) c p ↔ p = (a + c) / 2) ∧
    (∀ p : ℝ, marginalRevenue (linearDemand a b) p = 2 * p - a) ∧
    (∀ c : ℝ, c < a →
      elasticity (linearDemand a b) ((a + c) / 2) = (a + c) / (a - c)) ∧
    elasticity (linearDemand a b) (a / 2) = 1 ∧
    (∀ c c' : ℝ, 0 ≤ c → c < c' → c' < a →
      elasticity (linearDemand a b) ((a + c') / 2) / elasticity (linearDemand a b) ((a + c) / 2)
        > ((a + c') / 2) / ((a + c) / 2)) ∧
    (∀ c c' Δ : ℝ, 0 ≤ c → c < c' → 0 < Δ → c' + Δ < a →
      elasticity (linearDemand a b) ((a + (c' + Δ)) / 2) / elasticity (linearDemand a b) ((a + c') / 2)
        > elasticity (linearDemand a b) ((a + (c + Δ)) / 2) / elasticity (linearDemand a b) ((a + c) / 2)) := by sorry

end SpenglerVertical.DoubleMarginalization
