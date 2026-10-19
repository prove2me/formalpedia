-- Prove2me | Theorems.Thm_SecretaryAdvice_Samples_lemma_15
-- name    : SecretaryAdvice.Samples.lemma_15
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T00:41:14.861493+00:00
-- url     : https://prove2.me/theorems/8a4339fd-036d-4ded-a491-a97930733516
-- title:
--   Lemma 15, p. 15 — Σ_{s=u}^{v} ∏_{t=a+1}^{b} (s+t) = [∏_{t=a}^{b}(v+1+t) − ∏_{t=a}^{b}(u+t)]/(b−a+1)
-- statement:
--   For integers $a<b$ and $u<v$,
--   $$\sum_{s=u}^{v}\prod_{t=a+1}^{b}(s+t)=\frac{1}{b-a+1}\left[\prod_{t=a}^{b}(v+1+t)-\prod_{t=a}^{b}(u+t)\right].$$
--
--   This is a discrete integration formula for rising products. It evaluates the sums over signals that arise in the dual of the samples LP, in both claims of the proof of Theorem 16.
--
--   **Formalization Note** The sums and products range over integer intervals; both sides are computed in $\mathbb R$.
-- source:
--   Dütting et al., Secretaries with Advice, arXiv:2011.06726v1, p. 15, Lemma 15

import Mathlib
open Finset

namespace SecretaryAdvice.Samples

theorem lemma_15 (a b u v : ℤ) (hab : a < b) (huv : u < v) :
    ∑ s ∈ Icc u v, ∏ t ∈ Icc (a + 1) b, ((s + t : ℤ) : ℝ) =
      1 / ((b - a + 1 : ℤ) : ℝ) *
        (∏ t ∈ Icc a b, ((v + 1 + t : ℤ) : ℝ) - ∏ t ∈ Icc a b, ((u + t : ℤ) : ℝ)) := by sorry

end SecretaryAdvice.Samples
