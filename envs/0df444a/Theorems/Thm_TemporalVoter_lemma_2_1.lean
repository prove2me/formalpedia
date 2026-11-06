-- Prove2me | Theorems.Thm_TemporalVoter_lemma_2_1
-- name    : TemporalVoter.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:10:09.152387+00:00
-- url     : https://prove2.me/theorems/39263fc4-78fe-444c-bfb3-4f0c82e10fcb
-- title:
--   Lemma 2.1 — optional stopping for nonnegative supermartingales (corrected: X ≥ 0 and t ≤ τ added)
-- statement:
--   Let $(X_t:t\ge0)$ be a real supermartingale on a probability space with filtration $(\mathcal F_t:t\ge0)$ such that $X_t\ge0$ for all $t$. Let $\tau$ be a stopping time that is almost surely finite, and let $t\ge0$ with $t\le\tau$ almost surely. Then
--   $$\mathbb E(X_\tau\mid\mathcal F_t)\le X_t\qquad\text{almost surely.}$$
--
--   This is the form of optional stopping used in the proof of Theorem 3.1, applied at $t=0$ to the volume of the minority set and to a nonnegative potential.
--
--   Differences from the source:
--   - correction: (X_t) a supermartingale, τ an a.s. finite stopping time, t ≥ 0 → additionally X_t ≥ 0 for all t and t ≤ τ almost surely; reason: the printed lemma is false: the simple random walk from 0 with τ the hitting time of 1 and t = 0 gives E(X_τ | F_0) = 1 > 0; the deterministic X_t = 1/(t+1) with τ ≡ 0 and t = 1 gives 1 > 1/2. Every use in the paper satisfies both added hypotheses
--   - encoding: stopping time τ with values in ℕ → τ : Ω → WithTop ℕ (Mathlib's stopping times) with τ ≠ ⊤ almost surely; reason: Mathlib convention; X_τ is stoppedValue, the same on {τ < ∞}
-- source:
--   Rocha Avila, Dell, Lapinskas, Temporal Conductance and Bounds on the Voter Model for Dynamic Networks, arXiv:2606.13374 (2 Nov 2026), Lemma 2.1, p.12

import Mathlib

open MeasureTheory

namespace TemporalVoter

/-- **Lemma 2.1 (Optional stopping theorem), corrected** (Rocha Avila, Dell, Lapinskas,
arXiv:2606.13374, version of 2 Nov 2026, p.12): let `(X_t : t ≥ 0)` be a nonnegative
supermartingale with filtration `(𝓕_t)`, `τ` an almost surely finite stopping time and `t ≥ 0`
with `t ≤ τ` almost surely. Then `E(X_τ | 𝓕_t) ≤ X_t` almost surely.

**Formalization Note** As printed (without `X ≥ 0` and `t ≤ τ`) the lemma is false: the simple
random walk with `τ` the hitting time of `1` and `t = 0`, and the deterministic `X_t = 1/(t+1)`
with `τ ≡ 0`, `t = 1`. Both added hypotheses hold at every use in the paper. Stopping times take
values in `WithTop ℕ` (Mathlib). -/
theorem lemma_2_1 {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℕ m0} {X : ℕ → Ω → ℝ} (hX : Supermartingale X ℱ P)
    (hX_nonneg : ∀ n ω, 0 ≤ X n ω) {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime ℱ τ)
    (hτ_fin : ∀ᵐ ω ∂P, τ ω ≠ ⊤) (t : ℕ) (ht : ∀ᵐ ω ∂P, (t : WithTop ℕ) ≤ τ ω) :
    P[stoppedValue X τ | ℱ t] ≤ᵐ[P] X t := by sorry

end TemporalVoter
