-- Prove2me | Theorems.Thm_RefMNLPricing_Myopic_corollary_2
-- name    : RefMNLPricing.Myopic.corollary_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:10:14.765624+00:00
-- url     : https://prove2.me/theorems/06dd87c3-cb32-4729-8727-3dd3820e35a4
-- title:
--   Corollary 2, p. 16 — with only loss-neutral products the myopic policy has a unique steady state, given by (17)–(18), reached synchronously
-- statement:
--   Consider the MNL pricing model with reference effects in which every product is loss-neutral, $c_i := c_i^+ = c_i^-\ge0$, with $b_i>0$, memory $\alpha\in[0,1]$, price box $\mathcal P^n=[0,p_H]^n$, $p_H>0$, and the ceiling assumption $p_H\ge\hat p_H$. Let $p^m$ be any myopic pricing policy and, for $r^0\in\mathcal P^n$, let $r^{t+1}=\alpha r^t+(1-\alpha)p^m(r^t)$. Then:
--
--   1. The equation
--   $$
--   \Pi = \sum_{i\in N}\frac{1}{b_i+c_i}\exp\Big(a_i - b_i\Pi - \frac{b_i}{b_i+c_i}\Big) \qquad (18)
--   $$
--   has a unique solution $\Pi^{m\star}$.
--   2. If $\alpha<1$, the vector $p^{m\star}$ with
--   $$
--   p_i^{m\star} = \Pi^{m\star} + \frac{1}{b_i+c_i},\qquad i\in N, \qquad (17)
--   $$
--   lies in $\mathcal P^n$, is a steady state of $p^m$ ($p^m(p^{m\star}) = p^{m\star}$) and the only one in $\mathcal P^n$, and for every $r^0\in\mathcal P^n$ the myopic price path $p^m(r^t)$ converges to $p^{m\star}$ while the optimal single-period revenues $\Pi^m(r^t)=\Pi(p^m(r^t),r^t)$ converge to $\Pi^{m\star}$.
--   3. For every $r^0\in\mathcal P^n$ the convergence patterns of all products are synchronous: either every sequence $\{p_i^m(r^t)\}_t$ is non-decreasing, or every one is non-increasing, or there is a common time $T$ such that every one is non-increasing on $\{0,\dots,T\}$ and non-decreasing from $T$ on.
--
--   In the symmetric (loss-neutral) case the myopic steady state is thus explicit, independent of the initial reference price, and approached in lockstep across products.
--
--   **Formalization Note** At $\alpha=1$ the reference price never moves, so the price path is the constant $p^m(r^0)$, which is in general not $p^{m\star}$; part 2 therefore assumes $\alpha<1$ (the paper states it for $\alpha\in[0,1]$). Part 3 is stated for every $\alpha\in[0,1]$ (at $\alpha=1$ it holds trivially). "Synchronous" is encoded by one common case, and in case 3 one common turning time $T$, for all products; "monotone" is read non-strictly, so constant paths are allowed. $\Pi^{m\star}$ is bound as any solution of (18), which by part 1 is the unique one. Uniqueness of the steady state covers both its uniqueness as a fixed point of $p^m$ in $\mathcal P^n$ and its independence of $r^0$.
-- source:
--   Guo, Jiang, Shen, Multi-Product Dynamic Pricing with Reference Effects Under Logit Demand, SSRN 4189049 (version of 2024-05-25), p. 16, Corollary 2, (17)–(18); steady state p. 15; standing assumption §2.4, p. 11

import Mathlib
import Definitions.Def_RefMNLPricing_Myopic_Model

namespace RefMNLPricing.Myopic

open Filter Topology

/-- Corollary 2, p. 16 (all products loss-neutral, `c_i := c_i⁺ = c_i⁻`). Under the standing
assumptions and the ceiling assumption, for every myopic policy `pm`:
(a) equation (18), `Π = ∑_i 1/(b_i+c_i) · exp(a_i - b_i Π - b_i/(b_i+c_i))`, has a unique solution;
(b) if `α < 1` and `Π^{m⋆}` solves (18), then `p^{m⋆} := (Π^{m⋆} + 1/(b_i+c_i))_i` (17) lies in
`Pⁿ`, is the unique steady state of `pm` in `Pⁿ`, and from every `r⁰ ∈ Pⁿ` the myopic price path
converges to `p^{m⋆}` and the single-period revenues `Π^m(r^t)` converge to `Π^{m⋆}`;
(c) from every `r⁰ ∈ Pⁿ` the price paths of all products are, synchronously, all non-decreasing,
all non-increasing, or all non-increasing up to a common time `T` and non-decreasing from `T` on. -/
theorem corollary_2 {n : ℕ} (a b cp cm : Fin n → ℝ) (α pH : ℝ)
    (hb : ∀ i, 0 < b i) (hcp : ∀ i, 0 ≤ cp i) (hcm : ∀ i, 0 ≤ cm i)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hpH : 0 < pH) (hceil : CeilingOK a b cp cm pH)
    (hneutral : ∀ i, cp i = cm i)
    (pm : (Fin n → ℝ) → (Fin n → ℝ)) (hpm : IsMyopicSel a b cp cm pH pm) :
    (∃! v : ℝ, v = ∑ i, 1 / (b i + cp i) * Real.exp (a i - b i * v - b i / (b i + cp i))) ∧
    (∀ vs : ℝ, vs = ∑ i, 1 / (b i + cp i) * Real.exp (a i - b i * vs - b i / (b i + cp i)) →
      α < 1 →
        InBox pH (fun i => vs + 1 / (b i + cp i)) ∧
        pm (fun i => vs + 1 / (b i + cp i)) = (fun i => vs + 1 / (b i + cp i)) ∧
        (∀ x : Fin n → ℝ, InBox pH x → pm x = x → x = fun i => vs + 1 / (b i + cp i)) ∧
        ∀ r₀ : Fin n → ℝ, InBox pH r₀ →
          Tendsto (fun t => pm (myopicRef pm α r₀ t)) atTop
              (𝓝 (fun i => vs + 1 / (b i + cp i))) ∧
          Tendsto (fun t => revenue a b cp cm (pm (myopicRef pm α r₀ t)) (myopicRef pm α r₀ t))
              atTop (𝓝 vs)) ∧
    (∀ r₀ : Fin n → ℝ, InBox pH r₀ →
      (∀ i, Monotone (fun t => pm (myopicRef pm α r₀ t) i)) ∨
      (∀ i, Antitone (fun t => pm (myopicRef pm α r₀ t) i)) ∨
      (∃ T : ℕ, ∀ i, AntitoneOn (fun t => pm (myopicRef pm α r₀ t) i) (Set.Iic T) ∧
          MonotoneOn (fun t => pm (myopicRef pm α r₀ t) i) (Set.Ici T))) := by sorry

end RefMNLPricing.Myopic
