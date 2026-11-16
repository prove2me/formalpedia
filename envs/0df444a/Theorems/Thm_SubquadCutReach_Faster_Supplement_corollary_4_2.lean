-- Prove2me | Theorems.Thm_SubquadCutReach_Faster_Supplement_corollary_4_2
-- name    : SubquadCutReach.Faster.Supplement.corollary_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:23:49.492503+00:00
-- url     : https://prove2.me/theorems/5e0b9d98-a9dd-4cac-95fe-28b82a7745ee
-- title:
--   Corollary 4.2 — Optimised regret bound for Euclidean FTRL
-- statement:
--   Let $n\ge0$, let $D,L>0$ and let $T\ge1$ be an integer. Run Euclidean FTRL in $\mathbb R^n$ from $y_1=0$ with the update $y_{t+1}=y_t-\eta\ell_t$ and the step
--
--   $$\eta=\frac{D}{L\sqrt{2T}} .$$
--
--   If the loss vectors satisfy $\|\ell_t\|_2\le L$ in every round $t=1,\dots,T$, then simultaneously for every comparator $u$ with $\|u\|_2\le D$,
--
--   $$\mathrm{Reg}_T(u)=\sum_{t=1}^T\langle \ell_t,y_t\rangle-\sum_{t=1}^T\langle \ell_t,u\rangle\le DL\sqrt{2T}.$$
--
--   The losses may be arbitrary, including adaptively chosen ones. This bound drives the averaging guarantee of Lemma 3.7 and hence the warm-up protocol of Theorem 1.1. The paper derives it from a cited regret bound (Theorem 4.1, from Shalev-Shwartz), which is not assumed here.
--
--   Differences from the source:
--   - encoding: rounds $t=1,\dots,T$ with $y_1=0$ → 0-based rounds $t<T$ with `ftrlIter η ℓ 0 = 0`; reason: index shift only
--   - encoding: vectors in $\mathbb R^n$ with $\langle\cdot,\cdot\rangle$ and $\|\cdot\|_2$ → `EuclideanSpace ℝ (Fin n)` with Mathlib's inner product and norm; reason: the same inner product and norm
--   - encoding: loss vectors that may depend on the history → an arbitrary sequence `ℓ : ℕ → ℝ^n`, quantified universally; reason: each adaptive run is one fixed sequence, and the iterates use only past losses
-- source:
--   Henry Fleischmann, Sagnik Mukhopadhyay, Swagato Sanyal, STOC 2027 submission #503 (October 2026), p. 13, Corollary 4.2 (PDF p. 15)

import Definitions.Def_SubquadCutReach_Faster_Supplement_FTRL

set_option autoImplicit false

namespace SubquadCutReach.Faster.Supplement

/-- Corollary 4.2, p. 13 (PDF 15). Rounds `1..T` are `t ∈ range T`; the loss sequence is
arbitrary, which covers adaptively chosen losses. -/
theorem corollary_4_2 (n : ℕ) (D L : ℝ) (hD : 0 < D) (hL : 0 < L) (T : ℕ) (hT : 1 ≤ T)
    (ℓ : ℕ → EuclideanSpace ℝ (Fin n)) (hℓ : ∀ t < T, ‖ℓ t‖ ≤ L) :
    ∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ ≤ D →
      ftrlRegret (D / (L * Real.sqrt (2 * (T : ℝ)))) ℓ T u ≤ D * L * Real.sqrt (2 * (T : ℝ)) := by sorry

end SubquadCutReach.Faster.Supplement
