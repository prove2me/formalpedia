-- Prove2me | Theorems.Thm_RGGDetect_lemma_8
-- name    : RGGDetect.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:41:24.406196+00:00
-- url     : https://prove2.me/theorems/be31733d-caba-4cd4-a063-78b8c577d33f
-- title:
--   Lemma 8 — harmonic selection rule for $A_{h;\mathbf a}$
-- statement:
--   For the kernel $A_{h;\mathbf a}$ of (57) to be non-zero, it is necessary that
--
--   $$
--   q(h;\mathbf a)=\frac{h+\|\mathbf a\|_1}2\in\mathbb Z,\qquad q(h;\mathbf a)\ge\max\Big\{h,\max_{1\le j\le k}a_j\Big\}. \tag{58}
--   $$
--
--   Equivalently, the total degree is even, and none of the degrees $h,a_1,\dots,a_k$ exceeds the sum of all the others. In particular,
--
--   $$
--   A=\|\mathbf a\|_1\ge\max\{h,k\},\qquad s(h;\mathbf a)=\frac{\|\mathbf a\|_1-h}2\in\mathbb Z. \tag{59}
--   $$
--
--   The rule restricts the multidegrees that can appear in the cavity recurrence.
--
--   **Formalization Note** $d\ge2$; $u\notin S$, $|S|=k$, and $a_j\ge1$ for $j\in S$. "Non-zero" means not identically zero as a function of the configuration. The first conjunct is the "Equivalently" as an equivalence of the two conditions.
--
--   Differences from the source:
--   - encoding: Lemma 8 for the paper's d → d ≥ 2; reason: P_{ℓ,d} is defined only for d ≥ 2 (the recurrence divides by 0 at d = 1)
--   - encoding: a ∈ ℕ^k on the points x_S, u marked → a positive on a finite set S of vertices with u ∉ S, k = |S|; reason: indexing; ℕ = {1, 2, …} as in the proof
-- source:
--   Du, Mao, Sun, Wu, Xu, Sharp detection thresholds for random geometric graphs with polynomial average degrees, arXiv:2610.08517 (held version, sha256 e7bebd4a…), Lemma 8, eqs. (58)–(59), p.18 (PDF p.20)

import Mathlib
import Definitions.Def_RGGDetect_harmCoef

namespace RGGDetect

/-- **Lemma 8** (harmonic selection rule; arXiv:2610.08517, held version, sha256 e7bebd4a…, Lemma 8,
p.18, eqs. (58)–(59)): for the kernel `A_{h;a}` of (57) to be non-zero it is necessary that
`q(h; a) = (h + ‖a‖₁)/2 ∈ ℤ` and `q(h; a) ≥ max{h, max_j a_j}` (58). Equivalently, the total degree is
even and none of the degrees `h, a₁, …, a_k` exceeds the sum of all the others. In particular
`A = ‖a‖₁ ≥ max{h, k}` and `s(h; a) = (‖a‖₁ - h)/2 ∈ ℤ` (59).

**Formalization Note** The points are an `n`-point configuration; `u ∉ S` is the marked vertex and
`a = (a_j : j ∈ S)` has every `a_j ≥ 1`, `k = |S|`. "Non-zero" is "not identically zero". `d ≥ 2`, where
`P_{ℓ,d}` is defined. The first conjunct is the "Equivalently" (an equivalence of the two conditions),
the second is (58) and (59) for a non-zero kernel. -/
theorem lemma_8 (d : ℕ) (hd : 2 ≤ d) (n h : ℕ) (u : Fin n) (S : Finset (Fin n)) (hu : u ∉ S)
    (a : Fin n → ℕ) (ha : ∀ j ∈ S, 1 ≤ a j) :
    ((Even (h + ∑ j ∈ S, a j) ∧ 2 * h ≤ h + ∑ j ∈ S, a j ∧
        ∀ j ∈ S, 2 * a j ≤ h + ∑ i ∈ S, a i) ↔
      (Even (h + ∑ j ∈ S, a j) ∧ h ≤ ∑ j ∈ S, a j ∧
        ∀ j ∈ S, a j ≤ h + ∑ i ∈ S.erase j, a i)) ∧
    ((∃ x : Config n d, kernelA d h S a u x ≠ 0) →
      (Even (h + ∑ j ∈ S, a j) ∧ 2 * h ≤ h + ∑ j ∈ S, a j ∧
        ∀ j ∈ S, 2 * a j ≤ h + ∑ i ∈ S, a i) ∧
      (max h S.card ≤ ∑ j ∈ S, a j ∧ Even (∑ j ∈ S, a j - h))) := by sorry

end RGGDetect
