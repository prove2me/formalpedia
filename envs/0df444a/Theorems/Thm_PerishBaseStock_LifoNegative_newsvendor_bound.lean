-- Prove2me | Theorems.Thm_PerishBaseStock_LifoNegative_newsvendor_bound
-- name    : PerishBaseStock.LifoNegative.newsvendor_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T04:28:22.070227+00:00
-- url     : https://prove2.me/theorems/10437749-2e72-4d7b-9040-9e22f93c9103
-- title:
--   App. C.3, p. ec9 — $h\mathbb E[(S-D)^+]+p\mathbb E[(D-S)^+]\le p(\mathbb E[D]-\underline D)$ on $[\underline D,\min\{S^{NP},m\underline D\}]$
-- statement:
--   In the proof of Proposition 1, let $D$ be the demand, $\underline D$ its lower support, $S^{NP} = F^{-1}(p/(p+h))$ the newsvendor level, and $m \ge 2$ the lifetime, with $S^{NP} > \underline D > 0$. For every level $S$ with
--   $$\underline D \le S \le \min\{S^{NP}, m\underline D\},$$
--   the single-period holding and penalty cost satisfies
--   $$h\mathbb E[(S-D)^+] + p\mathbb E[(D-S)^+] \le p(\mathbb E[D] - \underline D).$$
--
--   In the cyclic policy of Appendix C.3 the order-up-to level of every period that is not $1, m+1, 2m+1,\dots$ lies in this interval, so this bounds the expected holding and penalty cost of those periods.
--
--   **Formalization Note** The left side is `backorderCost` of the published definition `LostSalesOrderUpTo.Asymptotic.Backorder` at the demand law. Levels are nonnegative reals. The proposition's standing hypotheses are explicit binders.
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, SSRN 3724966 (accepted manuscript, 2022), p. ec9, App. C.3 (Proof of Proposition 1), item 3) and its display

import Definitions.Def_PerishBaseStock_LifoNegative_Model

open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open CappedBaseStock LostSalesOrderUpTo.Asymptotic

namespace PerishBaseStock.LifoNegative

theorem newsvendor_bound (P : DemandLaw) (c : Params) (S : ℝ≥0)
    (hm : 2 ≤ c.m)
    (hNP : PerishBaseStock.Outdating.lowerSupport P < (newsvendorLevel P.law c.h c.p : ℝ))
    (hD : 0 < PerishBaseStock.Outdating.lowerSupport P)
    (hS₁ : PerishBaseStock.Outdating.lowerSupport P ≤ (S : ℝ))
    (hS₂ : (S : ℝ) ≤ min (newsvendorLevel P.law c.h c.p : ℝ) ((c.m : ℝ) * PerishBaseStock.Outdating.lowerSupport P)) :
    backorderCost P.law c.h c.p S ≤ c.p * (mean P - PerishBaseStock.Outdating.lowerSupport P) := by sorry

end PerishBaseStock.LifoNegative
