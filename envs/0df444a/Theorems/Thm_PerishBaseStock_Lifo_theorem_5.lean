-- Prove2me | Theorems.Thm_PerishBaseStock_Lifo_theorem_5
-- name    : PerishBaseStock.Lifo.theorem_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T01:06:23.032465+00:00
-- url     : https://prove2.me/theorems/85b27dbb-b061-49d6-96b2-639f5b343ada
-- title:
--   Theorem 5 — under LIFO, $\pi_{\hat S}$ has gap $\le3\theta E[(S^{NP}-D)^+]/(2m)$ and is asymptotically optimal in $p$ and $\theta$
-- statement:
--   Consider the perishable lost-sales inventory system with zero lead time and LIFO issuance: lifetime $m\ge 1$, unit holding cost $h>0$, unit penalty $p>0$, unit outdating cost $\theta\ge 0$, i.i.d. demands distributed as $D\ge 0$ with $0<\mathbb E[D]<\infty$. Let $\hat S$ be a minimizer over $[0,\infty)$ of $(\hat C_L(S)+\hat C_U(S))/2$, where
--   $$\hat C_L(S)=h\mathbb E[(S-D)^+]+p\mathbb E[(D-S)^+]+\frac{\theta}{m}\mathbb E[(S-\max\{D_1,\dots,D_m\})^+],\qquad\hat C_U(S)=\Big(h+\frac{\theta}{m}\Big)\mathbb E[(S-D)^+]+p\mathbb E[(D-S)^+],$$
--   and let $S^{NP}=F^{-1}(p/(p+h))$. Then:
--
--   1. **(a)** For every such $\hat S$,
--   $$C^{LIFO}(\hat S)-\mathrm{OPT}^{LIFO}\le\frac{3\theta\,\mathbb E[(S^{NP}-D)^+]}{2m}.$$
--   2. **(b)** If demand $D$ is unbounded, then, with $m,h,\theta$ fixed and $\hat S_p$ a minimizer for penalty $p$,
--   $$\lim_{p\to\infty}\frac{C^{LIFO}_p(\hat S_p)-\mathrm{OPT}^{LIFO}_p}{\mathrm{OPT}^{LIFO}_p}=0.$$
--   3. **(c)** If the demand lower support $\underline D=0$, then, with $m,h,p$ fixed and $\hat S_\theta$ a minimizer for outdating cost $\theta$,
--   $$\lim_{\theta\to\infty}\big(C^{LIFO}_\theta(\hat S_\theta)-\mathrm{OPT}^{LIFO}_\theta\big)=0.$$
--
--   The theorem gives the first performance guarantee for a base-stock policy in the LIFO perishable system: an absolute gap of order $1/m$ in the lifetime, relative optimality for large penalty, and absolute optimality for large outdating cost when demand can be arbitrarily small.
--
--   **Formalization Note** Costs are in $[0,\infty]$. Part (a) is stated as $C^{LIFO}(\hat S)\le\mathrm{OPT}^{LIFO}+B$. In (b) and (c) the conclusion also asserts the finiteness that makes the real-valued expressions meaningful: in (b), eventually in $p$, $C^{LIFO}_p(\hat S_p)<\infty$ and $0<\mathrm{OPT}^{LIFO}_p<\infty$, so the division by zero convention of real numbers plays no role; in (c), both costs are finite for every $\theta\ge0$. Limits quantify over every selection of minimizers $p\mapsto\hat S_p$, $\theta\mapsto\hat S_\theta$; the varying parameter is changed by record update and the others keep their standing assumptions. "Unbounded" is $F(x)<1$ for all $x$.
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, SSRN 3724966 (accepted manuscript, 2022), p. 16, Theorem 5 (a)–(c)

import Definitions.Def_PerishBaseStock_Lifo_Heuristic

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
open LostSalesOrderUpTo.Asymptotic

namespace PerishBaseStock.Lifo

/-- Theorem 5: (a) the gap bound `3θE[(S^NP - D)⁺]/(2m)`; (b) relative asymptotic optimality
as `p → ∞` for unbounded demand; (c) asymptotic optimality as `θ → ∞` when `D̲ = 0`. -/
theorem theorem_5 (P : CappedBaseStock.DemandLaw) :
    (∀ (c : Params), c.Standing → ∀ Sh : ℝ≥0, IsHatMinimizer P c Sh →
      baseStockCost P c Sh ≤
        OPT P c + ENNReal.ofReal (3 * c.θ * expectedHolding P.law (snp P c) / (2 * c.m))) ∧
    (DemandUnbounded P → ∀ (c : Params), c.Standing → ∀ Sh : ℝ → ℝ≥0,
      (∀ p : ℝ, 0 < p → IsHatMinimizer P { c with p := p } (Sh p)) →
        (∀ᶠ p in atTop, baseStockCost P { c with p := p } (Sh p) < ⊤ ∧
            0 < OPT P { c with p := p } ∧ OPT P { c with p := p } < ⊤) ∧
          Tendsto (fun p : ℝ => ((baseStockCost P { c with p := p } (Sh p)).toReal
              - (OPT P { c with p := p }).toReal) / (OPT P { c with p := p }).toReal)
            atTop (𝓝 0)) ∧
    (lowerSupport P = 0 → ∀ (c : Params), c.Standing → ∀ Sh : ℝ → ℝ≥0,
      (∀ θ : ℝ, 0 ≤ θ → IsHatMinimizer P { c with θ := θ } (Sh θ)) →
        (∀ θ : ℝ, 0 ≤ θ → baseStockCost P { c with θ := θ } (Sh θ) < ⊤ ∧
            OPT P { c with θ := θ } < ⊤) ∧
          Tendsto (fun θ : ℝ => (baseStockCost P { c with θ := θ } (Sh θ)).toReal
              - (OPT P { c with θ := θ }).toReal) atTop (𝓝 0)) := by sorry

end PerishBaseStock.Lifo
