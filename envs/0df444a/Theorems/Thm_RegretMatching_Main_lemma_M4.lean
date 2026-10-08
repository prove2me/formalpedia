-- Prove2me | Theorems.Thm_RegretMatching_Main_lemma_M4
-- name    : RegretMatching.Main.lemma_M4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:05:27.608385+00:00
-- url     : https://prove2.me/theorems/ad6253bc-685d-407b-9620-cb8c4841fb0a
-- title:
--   LEMMA (proof of Step M4), p. 1147 — 1-step transition differences ≤ β_n give w-step differences ≤ |B| Σ_{r=0}^{w} β_{n+r}
-- statement:
--   Let $B$ be a finite set and let $\kappa_X,\kappa_Y$ be the one-step conditional probabilities of two processes $(X_n)_{n\ge0}$, $(Y_n)_{n\ge0}$ on $B$ with $X_0=Y_0$:
--   $$\kappa_X(n;b_0,\dots,b_{n-1};b_n)=P[X_n=b_n\mid X_0=b_0,\dots,X_{n-1}=b_{n-1}],$$
--   and similarly for $Y$; for each $n\ge1$ and each $(b_0,\dots,b_{n-1})$ these are probability vectors on $B$. Assume
--   $$|\kappa_X(n;b_0,\dots,b_{n-1};b_n)-\kappa_Y(n;b_0,\dots,b_{n-1};b_n)|\le\beta_n$$
--   for all $n\ge1$ and all $b_0,\dots,b_n\in B$. Then for all $n\ge1$, $w\ge0$ and all $b_0,\dots,b_{n-1},b_{n+w}\in B$,
--   $$\big|P[X_{n+w}=b_{n+w}\mid X_0=b_0,\dots,X_{n-1}=b_{n-1}]-P[Y_{n+w}=b_{n+w}\mid Y_0=b_0,\dots,Y_{n-1}=b_{n-1}]\big|\le|B|\sum_{r=0}^{w}\beta_{n+r}.$$
--
--   The lemma converts bounds on one-step transition differences into bounds on multi-step ones; it is the tool for Step M4.
--
--   **Formalization Note.** The processes enter only through their conditional probabilities ("kernel form"): the $w$-step conditional probability is defined by the recursion of the paper's proof, $P[b_{n+w}\mid b_0..b_{n-1}]=\sum_{b_n}P[b_{n+w}\mid b_0..b_n]\,P[b_n\mid b_0..b_{n-1}]$ (`multiStep`). This avoids conditioning on null events.
-- source:
--   Hart and Mas-Colell, A simple adaptive procedure leading to correlated equilibrium, Econometrica 68 (2000), p. 1147, Appendix, proof of Step M4, LEMMA

import Mathlib
import Definitions.Def_RegretMatching_Main_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace RegretMatching.Main

theorem lemma_M4
    {B : Type} [Fintype B] (κX κY : (n : ℕ) → (Fin n → B) → B → ℝ)
    (hX_nonneg : ∀ n, 1 ≤ n → ∀ b b', 0 ≤ κX n b b')
    (hX_sum : ∀ n, 1 ≤ n → ∀ b, ∑ b', κX n b b' = 1)
    (hY_nonneg : ∀ n, 1 ≤ n → ∀ b b', 0 ≤ κY n b b')
    (hY_sum : ∀ n, 1 ≤ n → ∀ b, ∑ b', κY n b b' = 1)
    (β : ℕ → ℝ) (hβ : ∀ n, 1 ≤ n → ∀ b b', |κX n b b' - κY n b b'| ≤ β n) :
    ∀ n, 1 ≤ n → ∀ (w : ℕ) (b : Fin n → B) (b' : B),
      |multiStep κX n b w b' - multiStep κY n b w b'|
        ≤ (Fintype.card B : ℝ) * ∑ r ∈ Finset.range (w + 1), β (n + r) := by sorry

end RegretMatching.Main
