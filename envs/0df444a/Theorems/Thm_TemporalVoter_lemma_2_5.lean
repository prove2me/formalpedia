-- Prove2me | Theorems.Thm_TemporalVoter_lemma_2_5
-- name    : TemporalVoter.lemma_2_5
-- status  : Proved
-- author  : @iris
-- created : 2026-11-05T20:10:06.638903+00:00
-- url     : https://prove2.me/theorems/3bbdae25-2ebe-4217-a967-b2ef60ffda6a
-- title:
--   Lemma 2.5 — the minimum of two martingales is a supermartingale
-- statement:
--   Let $(M_t:t\ge0)$ and $(N_t:t\ge0)$ be real martingales with respect to the same filtration $(\mathcal F_t:t\ge0)$ on a probability space. Then
--   $$X_t:=\min\{M_t,N_t\}$$
--   defines a supermartingale $(X_t:t\ge0)$ with respect to $(\mathcal F_t)$.
--
--   It is used to pass from the martingales $\mathrm{Vol}(A_t)$, $\mathrm{Vol}(\overline{A_t})$ to the volume of the minority set.
--
--   Differences from the source: none.
-- source:
--   Rocha Avila, Dell, Lapinskas, Temporal Conductance and Bounds on the Voter Model for Dynamic Networks, arXiv:2606.13374 (2 Nov 2026), Lemma 2.5, p.13

import Mathlib

open MeasureTheory

namespace TemporalVoter

/-- **Lemma 2.5** (arXiv:2606.13374, version of 2 Nov 2026, p.13): if `(M_t)` and `(N_t)` are
discrete-time real martingales with respect to the same filtration `(𝓕_t)`, then
`X_t := min{M_t, N_t}` is a supermartingale with respect to `(𝓕_t)`. -/
theorem lemma_2_5 {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℕ m0} {M N : ℕ → Ω → ℝ} (hM : Martingale M ℱ P) (hN : Martingale N ℱ P) :
    Supermartingale (fun t ω => min (M t ω) (N t ω)) ℱ P := by sorry

end TemporalVoter
