-- Prove2me | Theorems.Thm_SpikyCVP_lemma_4_5
-- name    : SpikyCVP.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:52:10.919603+00:00
-- url     : https://prove2.me/theorems/22513727-c075-44ad-8e2b-da28e19331b7
-- title:
--   Lemma 4.5 — one posterior sample succeeds with probability $2^{-C_pn}$
-- statement:
--   Let $1<p<2$, $\mathcal L=\mathcal L(B)$ of rank $n$, $t\in\mathbb R^n$, $v^\ast$ a closest vector, $d=\mathrm{dist}_p(\mathcal L,t)$, $Y(s)$ the minimizers of $\sum_k y_k^2/s_k^2$ over $M=2\mathcal L+v^\ast-t$, and $C_p=2(2048/(p-1))^{2/p}$. For any $r>0$ and $x\in2\mathcal L+v^\ast$ with $\|x-t\|_p^p\le d^p+8n(2r)^p$,
--
--   $$\Pr_{S\sim P_{x-t,r}}\Big[\|y\|_p^p\le d^p+8nr^p\ \text{for every } y\in Y(S)\Big]\ge 2^{-C_pn}.$$
--
--   It is the progress step of the algorithm: from a vector within $8n(2r)^p$ of optimal, one sample of widths and one Euclidean minimization reach a vector within $8nr^p$, with probability $2^{-C_pn}$.
--
--   **Formalization Note** The statement bounds the measure of the complementary event by $1-2^{-C_pn}$, which implies the printed form for an outer measure of total mass $1$.
--
--   Differences from the source:
--   - encoding: Pr[event] ≥ 2^{−C_p n} → postMeasure(complement of the event) ≤ 1 − 2^{−C_p n}; reason: the posterior has total mass 1 (3.3); for an outer measure the complement form implies the printed one, and they agree on measurable events
--   - generalization: L ⊆ Zⁿ (assumed throughout §4 after scaling) → any real basis B ∈ ℝ^{n×n} with det B ≠ 0; reason: §4, p.18 says integrality is used only in Lemma 4.6; integer bases are a special case
-- source:
--   Aggarwal, Morolia, How to Round Spiky Balls into Submission; And Faster Algorithms For The Closest Vector Problem, STOC 2027 submission (manuscript sha256 535c3bcc…), Lemma 4.5, p.21 (PDF p.23)

import Mathlib
import Definitions.Def_SpikyCVP_post
import Definitions.Def_SpikyCVP_Ymin

open MeasureTheory PNormReg

namespace SpikyCVP

/-- **Lemma 4.5 (one posterior sample succeeds with probability `2^{−Cp n}`).**
Aggarwal, Morolia, *How to Round Spiky Balls into Submission; And Faster Algorithms For The Closest Vector
Problem*, STOC 2027 submission (manuscript sha256 535c3bcc…), Lemma 4.5, p.21 (PDF p.23).

Let `p ∈ (1, 2)`, `L = L(B)` of rank `n`, `t ∈ ℝⁿ`, `v∗` a closest vector, `d = distp(L, t)`, `Y(s)` the minimizers
of `Σ_k y_k²/s_k²` over `M = 2L + v∗ − t`, and `Cp = 2(2048/(p − 1))^{2/p}`. For any `r > 0` and `x ∈ 2L + v∗` such
that `∥x − t∥p^p ≤ d^p + 8n(2r)^p`,
`Pr_{S∼P_{x−t,r}} [∥y∥p^p ≤ d^p + 8nr^p for every y ∈ Y(S)] ≥ 2^{−Cp n}`.

**Formalization Note.** Stated as the bound `1 − 2^{−Cp n}` on the measure of the complementary event,
which for an outer measure of total mass `1` implies the printed form. `B` is any real basis with
`det B ≠ 0` (the integrality of §4 is used only in Lemma 4.6). -/
theorem lemma_4_5 {n : ℕ} (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : B.det ≠ 0) (t v : Fin n → ℝ) (hv : IsClosestVec p B t v) (r : ℝ) (hr : 0 < r)
    (x : Fin n → ℝ) (hx : x ∈ twoLPlus B v)
    (hxd : lpPow p (x - t) ≤ lpPow p (v - t) + 8 * n * (2 * r) ^ p) :
    postMeasure p (x - t) r
        {s | ∃ y ∈ Ymin B v t s, lpPow p (v - t) + 8 * n * r ^ p < lpPow p y} ≤
      ENNReal.ofReal (1 - (2 : ℝ) ^ (-(Cp p * n))) := by sorry

end SpikyCVP
