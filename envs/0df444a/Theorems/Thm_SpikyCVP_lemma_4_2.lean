-- Prove2me | Theorems.Thm_SpikyCVP_lemma_4_2
-- name    : SpikyCVP.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:51:52.112814+00:00
-- url     : https://prove2.me/theorems/19161cc3-e194-4a16-bc88-4b211962f54a
-- title:
--   Lemma 4.2 — at the optimum the sampled metric is good
-- statement:
--   Let $1<p<2$, let $\mathcal L=\mathcal L(B)$ be a lattice of rank $n$ in $\mathbb R^n$, $t\in\mathbb R^n$, $v^\ast$ a closest vector of $\mathcal L$ to $t$ in $\ell_p$, $d=\mathrm{dist}_p(\mathcal L,t)$, and $Y(s)$ the set of minimizers of $\sum_k y_k^2/s_k^2$ over $M=2\mathcal L+v^\ast-t$. For any $r>0$,
--
--   $$\Pr_{S\sim P_{v^\ast-t,r}}\Big[\|y\|_p^p-d^p\le 8nr^p\ \text{for every } y\in Y(S)\Big]\ge 1-2^n e^{-4n}.$$
--
--   It says that if the current vector were optimal, the widths sampled at it would make every Euclidean minimizer nearly optimal in $\ell_p$.
--
--   **Formalization Note** The statement bounds the measure of the complementary event (some $y\in Y(S)$ has $\|y\|_p^p-d^p>8nr^p$) by $2^ne^{-4n}$, which implies the printed form for an outer measure of total mass $1$.
--
--   Differences from the source:
--   - encoding: Pr[event] ≥ 1 − 2ⁿe^{−4n} → postMeasure(complement of the event) ≤ 2ⁿe^{−4n}; reason: the posterior has total mass 1 (3.3); for an outer measure the complement form implies the printed one, and they agree on measurable events
--   - generalization: L ⊆ Zⁿ (assumed throughout §4 after scaling) → any real basis B ∈ ℝ^{n×n} with det B ≠ 0; reason: §4, p.18 says integrality is used only in Lemma 4.6; integer bases are a special case
-- source:
--   Aggarwal, Morolia, How to Round Spiky Balls into Submission; And Faster Algorithms For The Closest Vector Problem, STOC 2027 submission (manuscript sha256 535c3bcc…), Lemma 4.2, p.19 (PDF p.21)

import Mathlib
import Definitions.Def_SpikyCVP_post
import Definitions.Def_SpikyCVP_Ymin

open MeasureTheory PNormReg

namespace SpikyCVP

/-- **Lemma 4.2 (at the optimum, the sampled metric is good).**
Aggarwal, Morolia, *How to Round Spiky Balls into Submission; And Faster Algorithms For The Closest Vector
Problem*, STOC 2027 submission (manuscript sha256 535c3bcc…), Lemma 4.2, p.19 (PDF p.21).

Let `p ∈ (1, 2)`, `L = L(B)` of rank `n`, `t ∈ ℝⁿ`, `v∗` a closest vector of `L` to `t` in `ℓp`, `d = distp(L, t)`,
and `Y(s)` the minimizers of `Σ_k y_k²/s_k²` over `M = 2L + v∗ − t`. For any `r > 0`,
`Pr_{S∼P_{v∗−t,r}} [∥y∥p^p − d^p ≤ 8nr^p for every y ∈ Y(S)] ≥ 1 − 2ⁿ e^{−4n}`.

**Formalization Note.** Stated as the bound `2ⁿe^{−4n}` on the measure of the complementary event (some
`y ∈ Y(S)` has `∥y∥p^p − d^p > 8nr^p`), which for an outer measure implies the printed form. `d^p` is
`∥v∗ − t∥p^p`. The paper takes `L ⊆ Zⁿ` in §4 but says this is used only in Lemma 4.6; here `B` is any real
basis with `det B ≠ 0`. -/
theorem lemma_4_2 {n : ℕ} (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : B.det ≠ 0) (t v : Fin n → ℝ) (hv : IsClosestVec p B t v) (r : ℝ) (hr : 0 < r) :
    postMeasure p (v - t) r
        {s | ∃ y ∈ Ymin B v t s, 8 * n * r ^ p < lpPow p y - lpPow p (v - t)} ≤
      ENNReal.ofReal (2 ^ n * Real.exp (-(4 * n))) := by sorry

end SpikyCVP
