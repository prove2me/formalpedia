-- Prove2me | Theorems.Thm_RefMNLPricing_MultiVsSingle_corollary_2
-- name    : RefMNLPricing.MultiVsSingle.corollary_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T11:43:01.853119+00:00
-- url     : https://prove2.me/theorems/da563472-f1a2-4072-acf1-d481b8ab0d87
-- title:
--   Corollary 2, p. 16 — loss-neutral myopic policy: unique steady state p_i^{m⋆} = Π^{m⋆} + 1/(b_i + c_i), convergence, synchronous patterns
-- statement:
--   Consider the multi-product model with all products loss-neutral, $c_i:=c_i^+=c_i^-$, under the standing assumptions $b>0$, $c\ge0$, $\alpha\in[0,1]$, $p_H>0$ and $p_H\ge\hat p_H$. Let $p^m$ be any myopic selection and $r^0\in\mathcal P^n$ any initial reference price, with myopic reference path $r^{t+1}=\alpha r^t+(1-\alpha)p^m(r^t)$.
--
--   1. The equation
--   $$
--   \Pi=\sum_{i\in N}\frac{1}{b_i+c_i}\exp\Big(a_i-b_i\Pi-\frac{b_i}{b_i+c_i}\Big)\qquad(18)
--   $$
--   has a unique solution $\Pi^{m\star}$.
--   2. The vector $p^{m\star}$ with $p_i^{m\star}=\Pi^{m\star}+1/(b_i+c_i)$ (17) lies in $\mathcal P^n$ and is the unique fixed point of $p^m$ in $\mathcal P^n$. If $\alpha<1$, then $p^m(r^t)\to p^{m\star}$ and $\Pi^m(r^t)=\Pi(p^m(r^t),r^t)\to\Pi^{m\star}$.
--   3. The price paths $\{p_i^m(r^t)\}_t$ are synchronous: either all are monotone increasing, or all are monotone decreasing, or there is one time $T$ such that every one of them decreases up to $T$ and increases from $T$ on.
--
--   In this mission, $p^{m\star}$ supplies the constant $\zeta_1$ of Theorem 7.
--
--   **Formalization Note.** The limit claims carry $\alpha<1$: at $\alpha=1$ the reference never moves and the path is constant at $p^m(r^0)$, which is in general not $p^{m\star}$. The fixed-point claim does not depend on $\alpha$. "Monotone" is read non-strictly, and "synchronous" is encoded by one disjunct and one turning time for all products. Every claim quantifies over all myopic selections.
-- source:
--   Guo, Jiang, Shen, Multi-Product Dynamic Pricing with Reference Effects Under Logit Demand, SSRN 4189049 (version of 2024-05-25), p. 16, Corollary 2, (17)–(18)

import Mathlib
import Definitions.Def_RefMNLPricing_MultiVsSingle_Model
open Filter Topology

namespace RefMNLPricing.MultiVsSingle

/-- Corollary 2, p. 16 (loss-neutral scenario `N = N_n`, `c_i := c_i⁺ = c_i⁻`), for every myopic
selection `pm` and every initial reference price `r₀ ∈ Pⁿ`:
(a) equation (18) has a unique solution `Π^{m⋆}`;
(b) the vector `p^{m⋆}_i = Π^{m⋆} + 1/(b_i + c_i)` of (17) is the unique fixed point of `pm` in `Pⁿ`,
and, for `α < 1`, the myopic price path converges to it and `Π^m(r^t)` converges to `Π^{m⋆}`;
(c) the price paths of all products are synchronously monotone increasing, monotone decreasing, or
first decreasing and then increasing (one common turning time). -/
theorem corollary_2 {n : ℕ} (a b cp cm : Fin n → ℝ) (α pH : ℝ)
    (hb : ∀ i, 0 < b i) (hcp : ∀ i, 0 ≤ cp i) (hcm : ∀ i, 0 ≤ cm i)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hpH : 0 < pH) (hceil : RefMNLPricing.Gap.CeilingOK a b cp cm pH)
    (hneutral : ∀ i, cp i = cm i)
    (pm : (Fin n → ℝ) → (Fin n → ℝ)) (hpm : RefMNLPricing.Gap.IsMyopicSel a b cp cm pH pm)
    (r₀ : Fin n → ℝ) (hr₀ : RefMNLPricing.Myopic.InBox pH r₀) :
    (∃! R : ℝ, R = ∑ i, 1 / (b i + cp i) * Real.exp (a i - b i * R - b i / (b i + cp i))) ∧
    (∀ Rs : ℝ, Rs = ∑ i, 1 / (b i + cp i) * Real.exp (a i - b i * Rs - b i / (b i + cp i)) →
      (RefMNLPricing.Myopic.InBox pH (fun i => Rs + 1 / (b i + cp i)) ∧
        pm (fun i => Rs + 1 / (b i + cp i)) = (fun i => Rs + 1 / (b i + cp i)) ∧
        ∀ x, RefMNLPricing.Myopic.InBox pH x → pm x = x → x = (fun i => Rs + 1 / (b i + cp i))) ∧
      (α < 1 →
        Tendsto (fun t => pm (RefMNLPricing.Myopic.myopicRef pm α r₀ t)) atTop
          (𝓝 (fun i => Rs + 1 / (b i + cp i))) ∧
        Tendsto (fun t => RefMNLPricing.Myopic.revenue a b cp cm (pm (RefMNLPricing.Myopic.myopicRef pm α r₀ t)) (RefMNLPricing.Myopic.myopicRef pm α r₀ t))
          atTop (𝓝 Rs))) ∧
    ((∀ i, Monotone (fun t => pm (RefMNLPricing.Myopic.myopicRef pm α r₀ t) i)) ∨
      (∀ i, Antitone (fun t => pm (RefMNLPricing.Myopic.myopicRef pm α r₀ t) i)) ∨
      (∃ T : ℕ, ∀ i, AntitoneOn (fun t => pm (RefMNLPricing.Myopic.myopicRef pm α r₀ t) i) (Set.Iic T) ∧
        MonotoneOn (fun t => pm (RefMNLPricing.Myopic.myopicRef pm α r₀ t) i) (Set.Ici T))) := by sorry

end RefMNLPricing.MultiVsSingle
