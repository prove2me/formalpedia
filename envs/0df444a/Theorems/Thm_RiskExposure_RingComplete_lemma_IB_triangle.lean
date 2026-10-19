-- Prove2me | Theorems.Thm_RiskExposure_RingComplete_lemma_IB_triangle
-- name    : RiskExposure.RingComplete.lemma_IB_triangle
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T04:12:18.773705+00:00
-- url     : https://prove2.me/theorems/2e6e6cee-b61c-4e24-b282-c5fe5a8b65e0
-- title:
--   Lemma I.B, Internet Appendix p. 27 — Σ_i (A_i)⁺ ≥ (Σ_i A_i − B)⁺ + B whenever B < max_i A_i
-- statement:
--   Let $A_1,\dots,A_n$ be finitely many real numbers ($n\ge1$) and let $B\in\mathbb R$ with $B<\max_i A_i$. Then
--   $$\sum_i (A_i)^+\ \ge\ \Big(\sum_iA_i-B\Big)^+ + B .$$
--
--   The paper calls this a triangle inequality for the positive part. In the proof of Proposition 4 it moves the positive part outside the sum over the ring's possible payments, which reduces the comparison of the two distortions to the identities of Lemma I.A.
--
--   **Formalization Note.** "Any sequence $\{A_i\}$" is a finite nonempty family indexed by a `Finset`, which is how the proof of Proposition 4 uses it; $\max_i A_i$ is `Finset.sup'`. The inequality holds for every real family; no sign condition on the $A_i$ is assumed.
-- source:
--   Shu, Endogenous Risk Exposure and Systemic Instability, Management Science, doi:10.1287/mnsc.2022.01519 (accepted manuscript, 17 Sep 2024), Internet Appendix p. 27, Lemma I.B

import Mathlib

namespace RiskExposure.RingComplete

theorem lemma_IB_triangle {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (A : ι → ℝ) (B : ℝ)
    (hB : B < s.sup' hs A) :
    max (∑ i ∈ s, A i - B) 0 + B ≤ ∑ i ∈ s, max (A i) 0 := by sorry

end RiskExposure.RingComplete
