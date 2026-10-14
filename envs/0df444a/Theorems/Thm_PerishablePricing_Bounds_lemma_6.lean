-- Prove2me | Theorems.Thm_PerishablePricing_Bounds_lemma_6
-- name    : PerishablePricing.Bounds.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T21:16:05.238803+00:00
-- url     : https://prove2.me/theorems/734619b1-32b3-47c4-a0c3-20249764193f
-- title:
--   Lemma 6, p. 290 (k = 0) — f_t(s) is nonincreasing in each of s₁, …, s_{l−1}
-- statement:
--   Consider the backlogging perishable inventory–pricing model with lifetime $l\ge 2$ and zero lead time, under the standing assumptions of §3. Let $f_t$ be the profit-to-go of (4), for any $t=1,\dots,T+1$.
--
--   For every state $s\in\mathcal S$, every coordinate $i\in\{1,\dots,l-1\}$ and every $x\ge s_i$ such that the state $s'$ obtained from $s$ by replacing $s_i$ with $x$ is still in $\mathcal S$,
--
--   $$f_t(s')\le f_t(s).$$
--
--   That is, $f_t$ is nonincreasing in each of $s_1,\dots,s_{l-1}$ on $\mathcal S$ (for lead time $k=0$, the paper's $s_1,\dots,s_{l-k-1}$ are all coordinates). It is what makes the continuation term of $G_t$ nonincreasing in the order-up-to level.
--
--   **Formalization Note.** Time is counted in periods to go (`f n`, every `n`, covers $t=1,\dots,T+1$). Coordinates are 0-based (`i : Fin L`, $L=l-1$). The lemma holds in both the backlogging and the lost-sales cases in the paper; only the backlogging model is formalized here.
-- source:
--   Chen, Pang, Pan, Coordinating Inventory Control and Pricing Strategies for Perishable Products, Oper. Res. 62(2), 2014, Lemma 6, p. 290, with lead time k = 0

import Mathlib
import Definitions.Def_PerishablePricing_Bounds_Model

namespace PerishablePricing.Bounds

/-- Lemma 6 (p. 290) at lead time `k = 0`: for every number of periods to go `n` (the paper's
`t = 1, …, T + 1`) the profit-to-go `f_t` is nonincreasing in each coordinate `s₁, …, s_{l−1}` of the
state on `𝒮`: raising coordinate `i` of `s ∈ 𝒮` to `x ≥ s_i`, inside `𝒮`, does not increase `f_t`. -/
theorem lemma_6 (M : Model) (hM : M.Standing) (L : ℕ) (hL : 1 ≤ L) (n : ℕ)
    (s : Fin L → ℝ) (hs : s ∈ stateSpace L) (i : Fin L) (x : ℝ) (hx : s i ≤ x)
    (hs' : Function.update s i x ∈ stateSpace L) :
    M.f n (Function.update s i x) ≤ M.f n s := by sorry

end PerishablePricing.Bounds
