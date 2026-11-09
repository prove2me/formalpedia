-- Prove2me | Theorems.Thm_SkipListConc_lemma_4_13
-- name    : SkipListConc.lemma_4_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:55:40.410975+00:00
-- url     : https://prove2.me/theorems/d7ad3a56-7658-492a-b891-0d3acee3d3c8
-- title:
--   Lemma 4.13 — counting the vertical cost two ways: $W_{\mathrm{lev}}=D(L)$
-- statement:
--   Fix $0<p<1$, an operation sequence $\sigma$ and a cutoff $L\ge1$. Then, on every outcome,
--   $$
--   W_{\mathrm{lev}}=D(L)=\sum_xD_x(L).
--   $$
--
--   The identity lets Lemma 4.7, stated for $D(L)$, be applied to the backward walks.
--
--   Differences from the source:
--   - generalization: heights following Definition 1.1 → every realization ξ of the randomness (no law assumed); reason: the identity is deterministic; the source's case is an instance
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), Lemma 4.13, p.29

import Mathlib
import Definitions.Def_SkipListConc_Wlev
import Definitions.Def_SkipListConc_vertCost

namespace SkipListConc

/-- Lemma 4.13 (counting the vertical cost two ways) (Kapoor–Tanveer, *Counter-Free
Self-Adjusting Skip Lists: Concentration Bounds*, STOC 2027 submission manuscript (sha256
f82c3d35…6dab6c), Lemma 4.13, p.29). `W_lev = D(L) = ∑_x D_x(L)`.

**Formalization Note** An identity on every outcome, for every cutoff `L ≥ 1` and every noise
realization `ξ`. -/
theorem lemma_4_13 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) {K : ℕ} {α Ω : Type*} [DecidableEq α]
    (ξ : α × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ) (σ : List α) (L : ℕ) (hL : 1 ≤ L) :
    ∀ ω : Ω, Wlev p ξ σ L ω = vertCost p ξ σ L ω := by sorry

end SkipListConc
