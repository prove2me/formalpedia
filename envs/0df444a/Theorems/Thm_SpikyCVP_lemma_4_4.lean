-- Prove2me | Theorems.Thm_SpikyCVP_lemma_4_4
-- name    : SpikyCVP.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:52:19.89047+00:00
-- url     : https://prove2.me/theorems/c6764ae9-0b12-4fd5-8676-0d3b27c73537
-- title:
--   Lemma 4.4 — the posteriors at $v^\ast-t$ and $x-t$ overlap
-- statement:
--   Let $1<p<2$, $\mathcal L=\mathcal L(B)$ of rank $n$, $t\in\mathbb R^n$, $v^\ast$ a closest vector, $d=\mathrm{dist}_p(\mathcal L,t)$ and $r>0$. Let $0<\tau\le1/2$ and let $x\in 2\mathcal L+v^\ast$ be such that $\|x-t\|_p^p\le d^p+8n(2r)^p$. Then
--
--   $$I_\tau:=\int P_{v^\ast-t,r}(s)^{1-\tau}P_{x-t,r}(s)^{\tau}\,ds\ \ge\ \exp\Big(-\frac{1024\,\tau^{p/2}n}{p-1}\Big).$$
--
--   This is the step that replaces the parallelogram identity of the Euclidean case: when the current vector is close to optimal, the widths sampled at it are, with probability $2^{-O(n)}$, also good widths for the optimum.
--
--   **Formalization Note** The densities vanish off the open orthant, so the integral over $\mathbb R^n$ is the paper's.
--
--   Differences from the source:
--   - generalization: L ⊆ Zⁿ (assumed throughout §4 after scaling) → any real basis B ∈ ℝ^{n×n} with det B ≠ 0; reason: §4, p.18 says integrality is used only in Lemma 4.6; integer bases are a special case
--   - encoding: r > 0 fixed by the context of P_{·,r} → hypothesis 0 < r; reason: the posterior is defined only for r > 0 (§3)
-- source:
--   Aggarwal, Morolia, How to Round Spiky Balls into Submission; And Faster Algorithms For The Closest Vector Problem, STOC 2027 submission (manuscript sha256 535c3bcc…), Lemma 4.4, p.20 (PDF p.22)

import Mathlib
import Definitions.Def_SpikyCVP_post

open MeasureTheory PNormReg

namespace SpikyCVP

/-- **Lemma 4.4 (the posteriors overlap).**
Aggarwal, Morolia, *How to Round Spiky Balls into Submission; And Faster Algorithms For The Closest Vector
Problem*, STOC 2027 submission (manuscript sha256 535c3bcc…), Lemma 4.4, p.20 (PDF p.22).

Let `p ∈ (1, 2)`, `L = L(B)` of rank `n`, `t ∈ ℝⁿ`, `v∗` a closest vector, `d = distp(L, t)`, `r > 0`. Let
`0 < τ ≤ 1/2` and let `x ∈ 2L + v∗` be such that `∥x − t∥p^p ≤ d^p + 8n(2r)^p`. Then
`Iτ := ∫ P_{v∗−t,r}(s)^{1−τ} P_{x−t,r}(s)^τ ds ≥ exp(−1024 τ^{p/2} n / (p − 1))`.

**Formalization Note.** The densities vanish off the open orthant, so the integral over `ℝⁿ` is the paper's
integral over `R^n_{>0}`. A junk value `0` of the integral would only make the bound false. `B` is any real
basis with `det B ≠ 0` (the integrality of §4 is used only in Lemma 4.6). -/
theorem lemma_4_4 {n : ℕ} (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : B.det ≠ 0) (t v : Fin n → ℝ) (hv : IsClosestVec p B t v) (r : ℝ) (hr : 0 < r)
    (τ : ℝ) (hτ0 : 0 < τ) (hτ : τ ≤ 1 / 2) (x : Fin n → ℝ) (hx : x ∈ twoLPlus B v)
    (hxd : lpPow p (x - t) ≤ lpPow p (v - t) + 8 * n * (2 * r) ^ p) :
    Real.exp (-(1024 * τ ^ (p / 2) * n / (p - 1))) ≤
      ∫ s, post p (v - t) r s ^ (1 - τ) * post p (x - t) r s ^ τ := by sorry

end SpikyCVP
