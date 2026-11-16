-- Prove2me | Theorems.Thm_SubadditiveMMS580_Amplification_Supplement_lemma_5_1
-- name    : SubadditiveMMS580.Amplification.Supplement.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:58:33.492896+00:00
-- url     : https://prove2.me/theorems/039f1722-d4a8-471f-928d-96ccd4722bb0
-- title:
--   Lemma 5.1 — additive rounding loses at most the largest coefficient: $\tilde v_i(B_i)\ge\sum_g\tilde v_i(g)f_{ig}-\|\tilde v_i\|_\infty$
-- statement:
--   Let $\tilde v_1,\dots,\tilde v_r$ be nonnegative additive valuations on a finite set $M$, given by coefficients $\tilde v_i(g)\ge0$, and let $f$ be a **fractional allocation**: numbers $f_{ig}\ge0$ with $\sum_i f_{ig}\le1$ for every good $g$. Then there are pairwise disjoint bundles $B_1,\dots,B_r\subseteq M$ such that every agent $i$ satisfies
--   $$\tilde v_i(B_i)\ge\sum_{g\in M}\tilde v_i(g)\,f_{ig}-\|\tilde v_i\|_\infty,$$
--   where $\|\tilde v_i\|_\infty=\max_{g\in M}\tilde v_i(g)$ (zero when $M$ is empty).
--
--   This rounding step converts the fractional auxiliary value in the reservation theorem (Theorem 5.2) into integral bundles.
--
--   Differences from the source:
--   - encoding: agents i (any finite number) → agents Fin r for an arbitrary r ≥ 0; reason: same instances; r = 0 is trivial
-- source:
--   Bo Li, Ankang Sun, Toward Constant-Factor Maximin Share Guarantees for Subadditive Valuations, STOC 2027 submission #580 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/580.pdf, sha256 7de124b5706e9e49301a281a1eb418a8ae32d04bf4cf0941b969cc3cde85e485, Lemma 5.1, p. 31 (PDF p. 31)

import Mathlib
import Definitions.Def_SubadditiveMMS580_Amplification_Supplement_Reservation
import Definitions.Def_MultiAllocToAlloc_Subadditive_Valuation
import Definitions.Def_MultiAllocToAlloc_Subadditive_Allocation

open MultiAllocToAlloc.Subadditive MeasureTheory

namespace SubadditiveMMS580.Amplification.Supplement

/-- Lemma 5.1 (Li–Sun, STOC 2027 submission #580, p. 31): let `ṽ_i` (`i` among `r` agents) be
nonnegative additive valuations on the finite set `M = Fin m` and `f` a fractional allocation
(`f_ig ≥ 0`, `∑_i f_ig ≤ 1` for every good `g`). There are pairwise disjoint bundles `B_i ⊆ M`
with `ṽ_i(B_i) ≥ ∑_{g ∈ M} ṽ_i(g) f_ig − ‖ṽ_i‖∞` for every agent `i`. -/
theorem lemma_5_1 {r m : ℕ} (vt : Fin r → Fin m → ℝ) (hvt : ∀ i g, 0 ≤ vt i g)
    (f : Fin r → Fin m → ℝ) (hf : ∀ i g, 0 ≤ f i g) (hfsum : ∀ g, ∑ i, f i g ≤ 1) :
    ∃ B : Fin r → Finset (Fin m), IsAllocation B ∧
      ∀ i : Fin r, ∑ g, vt i g * f i g - supNorm (vt i) ≤ ∑ g ∈ B i, vt i g := by sorry

end SubadditiveMMS580.Amplification.Supplement
