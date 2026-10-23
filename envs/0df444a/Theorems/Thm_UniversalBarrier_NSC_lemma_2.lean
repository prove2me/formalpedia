-- Prove2me | Theorems.Thm_UniversalBarrier_NSC_lemma_2
-- name    : UniversalBarrier.NSC.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:36:36.043812+00:00
-- url     : https://prove2.me/theorems/8fa4b838-9b77-4101-a678-809b2c1b7081
-- title:
--   Lemma 2, p. 11 — a non-increasing density on [0, 1] has mean at most 1/2
-- statement:
--   Let $q$ be a probability density on $\mathbb R$ that vanishes outside $[0,1]$ and is non-increasing on $[0,1]$. Then its mean is at most $\tfrac12$:
--   $$\mu_1(q)=\int_{-\infty}^{\infty}t\,q(t)\,dt\ \le\ \frac12.$$
--
--   The lemma is used in §4.1.6 to discard the case $\alpha<0$ in the proof of inequality (5).
--
--   **Formalization Note.** "Distribution supported on $[0,1]$" is $q\ge0$, $q=0$ off $[0,1]$ and $\int q=1$; "non-increasing" is monotonicity on $[0,1]$.
-- source:
--   Lee & Yue, Universal Barrier is n-Self-Concordant, arXiv:1809.03011v4, p. 11, Lemma 2

import Mathlib
import Definitions.Def_UniversalBarrier_NSC_Model

open MeasureTheory

namespace UniversalBarrier.NSC

theorem lemma_2 (q : ℝ → ℝ) (hq0 : ∀ t, 0 ≤ q t) (hsupp : ∀ t ∉ Set.Icc (0 : ℝ) 1, q t = 0)
    (hmono : AntitoneOn q (Set.Icc 0 1)) (hq1 : ∫ t, q t = 1) :
    mu1 q ≤ 1 / 2 := by sorry

end UniversalBarrier.NSC
