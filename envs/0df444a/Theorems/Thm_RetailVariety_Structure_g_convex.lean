-- Prove2me | Theorems.Thm_RetailVariety_Structure_g_convex
-- name    : RetailVariety.Structure.g_convex
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:40:57.999888+00:00
-- url     : https://prove2.me/theorems/36e64339-127a-4694-b150-0db339ee762a
-- title:
--   Appendix: $g_I$ of (10) and $g_T$ of (11) are convex in $\delta$ on $[0,v_1]$
-- statement:
--   Let $v_1\ge v_2\ge\cdots\ge v_n$ be positive preferences ($n\ge1$), $v_0>0$, $0<c<p$, $\lambda>0$, $\sigma>0$, $0\le\beta<1$, and let $S\subseteq N$ be any assortment. Then the functions
--   $$g_I(\delta)=(p-c)\lambda\Bigl(\sum_{j\in S}v_j+\delta\Bigr)-\frac{p\sigma\lambda^\beta e^{-z^2/2}}{\sqrt{2\pi}}\Bigl(\sum_{j\in S}v_j^\beta+\delta^\beta\Bigr)\Bigl(\sum_{j\in S}v_j+\delta+v_0\Bigr)^{1-\beta}$$
--   and
--   $$g_T(\delta)=\lambda\Bigl[\sum_{j\in S}\bigl(pv_j-cf(\delta)\bigr)^++\bigl(p\delta-cf(\delta)\bigr)^+\Bigr],\qquad f(\delta)=\sum_{j\in S}v_j+\delta+v_0,$$
--   are convex on the interval $0\le\delta\le v_1$, where $z=\Phi^{-1}(1-c/p)$.
--
--   Together with the affinity and positivity of $f$, this is the hypothesis of Mangasarian's ratio result in the proof of Lemma 1.
--
--   **Formalization Note** $v_1$ is the first (most popular) variant, `v ⟨0, hn⟩`, not the no-purchase preference $v_0$ (`v0`). $g_T$ carries $\lambda$ on both terms (see the model's note on (11)).
-- source:
--   van Ryzin & Mahajan, On the Relationship Between Inventory Costs and Variety Benefits in Retail Assortments, Management Science 45(11), 1999, pp. 1507–1508, Appendix, proof of Lemma 1

import Mathlib
import Definitions.Def_RetailVariety_Structure_Model

namespace RetailVariety.Structure

/-- Appendix, proof of Lemma 1 (pp. 1507–1508): for any `S`, the functions `g_I` of (10) and
`g_T` of (11) are convex in `δ` on `[0, v_1]` (`v_1 = v ⟨0, hn⟩`, the most popular variant). -/
theorem g_convex (n : ℕ) (hn : 0 < n) (v : Fin n → ℝ) (v0 : ℝ) (hv : ∀ j, 0 < v j)
    (hv0 : 0 < v0) (hanti : Antitone v) (p c lam σ β : ℝ) (hc : 0 < c) (hcp : c < p)
    (hlam : 0 < lam) (hσ : 0 < σ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (S : Finset (Fin n)) :
    ConvexOn ℝ (Set.Icc 0 (v ⟨0, hn⟩)) (gI p c lam σ β v v0 S) ∧
      ConvexOn ℝ (Set.Icc 0 (v ⟨0, hn⟩)) (gT p c lam v v0 S) := by sorry

end RetailVariety.Structure
