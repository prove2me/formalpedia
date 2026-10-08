-- Prove2me | Theorems.Thm_RetailVariety_Structure_lemma_1
-- name    : RetailVariety.Structure.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:40:52.950232+00:00
-- url     : https://prove2.me/theorems/aeb6d117-e595-4bd7-89a0-82e02fde431d
-- title:
--   Lemma 1: $h_I=g_I/f$ and $h_T=g_T/f$ are quasi-convex in $\delta$ on $[0,v_1]$
-- statement:
--   Let $v_1\ge v_2\ge\cdots\ge v_n$ be positive preferences ($n\ge1$), $v_0>0$ the no-purchase preference, $0<c<p$, $\lambda>0$, $\sigma>0$, $0\le\beta<1$, $z=\Phi^{-1}(1-c/p)$, and let $S\subseteq N$ be any assortment. With $f$, $g_I$, $g_T$ as in (9)–(11), the functions
--   $$h_I(\delta)=\frac{g_I(\delta)}{f(\delta)},\qquad h_T(\delta)=\frac{g_T(\delta)}{f(\delta)}$$
--   are both quasi-convex on $0\le\delta\le v_1$: every sublevel set $\{\delta\in[0,v_1]:h(\delta)\le r\}$ is an interval.
--
--   $h_I(\delta)$ and $h_T(\delta)$ are the store profits after a variant of preference $\delta$ is added to $S$. Quasi-convexity means the maximum over an interval of $\delta$ is attained at an end point, which drives the exchange argument of Theorem 1.
--
--   **Formalization Note** The paper's $v_1$ is the first variant, `v ⟨0, hn⟩`; the paper's $v_0$ is `v0`. $g_T$ carries $\lambda$ on both terms; as printed in (11) $\lambda$ multiplies only the sum, which does not change quasi-convexity.
-- source:
--   van Ryzin & Mahajan, On the Relationship Between Inventory Costs and Variety Benefits in Retail Assortments, Management Science 45(11), 1999, p. 1503, Lemma 1, eqs. (9)–(11)

import Mathlib
import Definitions.Def_RetailVariety_Structure_Model

namespace RetailVariety.Structure

/-- Lemma 1, p. 1503: for any `S`, `h_I = g_I / f` and `h_T = g_T / f` are quasi-convex in
`δ` on `0 ≤ δ ≤ v_1` (`v_1 = v ⟨0, hn⟩`, the most popular variant; `v0` is the no-purchase
preference `v_0`). -/
theorem lemma_1 (n : ℕ) (hn : 0 < n) (v : Fin n → ℝ) (v0 : ℝ) (hv : ∀ j, 0 < v j)
    (hv0 : 0 < v0) (hanti : Antitone v) (p c lam σ β : ℝ) (hc : 0 < c) (hcp : c < p)
    (hlam : 0 < lam) (hσ : 0 < σ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (S : Finset (Fin n)) :
    QuasiconvexOn ℝ (Set.Icc 0 (v ⟨0, hn⟩)) (hI p c lam σ β v v0 S) ∧
      QuasiconvexOn ℝ (Set.Icc 0 (v ⟨0, hn⟩)) (hT p c lam v v0 S) := by sorry

end RetailVariety.Structure
