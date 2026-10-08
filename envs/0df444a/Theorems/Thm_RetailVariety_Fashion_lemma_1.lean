-- Prove2me | Theorems.Thm_RetailVariety_Fashion_lemma_1
-- name    : RetailVariety.Fashion.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:59:08.01777+00:00
-- url     : https://prove2.me/theorems/d9edb981-140d-4d4b-b888-3c93e85689dd
-- title:
--   Lemma 1 — $h_I(\delta)$ and $h_T(\delta)$ are quasi-convex on $[0, v_1]$
-- statement:
--   Consider a category with preferences $v_1\ge v_2\ge\cdots\ge v_n\ge 0$, $n\ge 1$, no-purchase preference $v_0>0$, and model parameters $0<c<p$, $\lambda>0$, $\sigma>0$, $0\le\beta<1$. Let $S$ be any set of variants, and let $f$, $g_I$, $g_T$, $h_I=g_I/f$, $h_T=g_T/f$ be the functions (9)–(11) of Lemma 1. Then
--   $$h_I \text{ and } h_T \text{ are quasi-convex on } [0,v_1],$$
--   that is, for every $\alpha$ the sets $\{\delta\in[0,v_1]: h(\delta)\le\alpha\}$ are intervals.
--
--   Quasi-convexity means that the profit of adding a variant to $S$, as a function of the added preference, is maximized at an end point. In the proof of Theorem 3 it is applied to the category $w$ with $S=A_{t-1}$.
--
--   **Formalization Note.** This restates Lemma 1 of mission I of this series inside this mission's namespace (draft items cannot import each other). The decreasing order of §3.1 is a hypothesis, so that $v_1$ (index 0 in Lean) is the largest preference. $\beta=0$ is allowed.
-- source:
--   van Ryzin & Mahajan, On the Relationship Between Inventory Costs and Variety Benefits in Retail Assortments, Management Science 45(11), 1999, p. 1503, Lemma 1

import Mathlib
import Definitions.Def_RetailVariety_Fashion_Lemma1Functions

namespace RetailVariety.Fashion

/-- Lemma 1 (p. 1503), restated: for preferences sorted decreasingly (§3.1), any set `S` of
variants and `0 ≤ δ ≤ v_1`, the functions `h_I = g_I/f` and `h_T = g_T/f` are quasi-convex in `δ`. -/
theorem lemma_1 {n : ℕ} (p c lam σ β v0 : ℝ) (hc : 0 < c) (hcp : c < p) (hlam : 0 < lam)
    (hσ : 0 < σ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hv0 : 0 < v0)
    (v : Fin n → ℝ) (hv : ∀ j, 0 ≤ v j) (hva : Antitone v) (hn : 0 < n) (S : Finset (Fin n)) :
    QuasiconvexOn ℝ (Set.Icc 0 (v ⟨0, hn⟩)) (hI p c lam σ β v v0 S) ∧
      QuasiconvexOn ℝ (Set.Icc 0 (v ⟨0, hn⟩)) (hT p c lam v v0 S) := by sorry

end RetailVariety.Fashion
