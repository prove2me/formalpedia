-- Prove2me | Theorems.Thm_RandOrderSort_lemma_4_6
-- name    : RandOrderSort.lemma_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:03:12.454196+00:00
-- url     : https://prove2.me/theorems/39f037e1-7c53-4675-b479-448d80fec3da
-- title:
--   Lemma 4.6 — witnesses at power-of-two scales
-- statement:
--   Let $(E_h)_{h\in\{1,2,4,\dots\}}$ be events with arbitrary dependence. Suppose that, possibly conditional on a sub-$\sigma$-field $\mathcal H$,
--   $$\mathbb P(E_h\mid\mathcal H)\le A_*e^{-a_*h}\qquad(h\ge h_*),$$
--   where $A_*,a_*,h_*>0$ are deterministic constants. For every fixed $c_*>0$ and $0<\eta<a_*/(2c_*)$,
--   $$\mathbb E\Bigl[\exp\Bigl(\eta c_*\sum_hh\mathbf 1[E_h]\Bigr)\Bigm|\mathcal H\Bigr]\le K_*,$$
--   where $K_*<\infty$ depends only on the displayed constants.
--
--   No independence between the events is needed, which is what allows dependent overflow witnesses to be combined.
--
--   **Formalization Note** $K_*$ is chosen after $(A_*,a_*,h_*,c_*,\eta)$ and before the probability space, the $\sigma$-field and the events. The unconditional case is $\mathcal H=\bot$.
--
--   Differences from the source:
--   - encoding: P(E_h | H) ≤ c and E[Y | H] ≤ K almost surely → the defining inequalities μ(E ∩ G) ≤ c μ(G) and ∫_G Y ≤ K μ(G) for every G in H; reason: equivalent for Y ≥ 0
--   - encoding: the possibly infinite sum over all scales → every finite truncation, with K independent of the truncation, as a lower integral; reason: monotone convergence gives the infinite sum, as in the page's proof
-- source:
--   Kang, Fan, Optimal High Probability Bounds for Random Order Online Sorting, arXiv:2610.15438 (version of 2026-11-01), Lemma 4.6, p.24, display (29)

import Mathlib
open MeasureTheory

namespace RandOrderSort

/-- **Lemma 4.6 (Witnesses at power-of-two scales)**, Kang, Fan, *Optimal High Probability Bounds for Random Order Online Sorting*, arXiv:2610.15438 (version of 2026-11-01), p.24: "Let (E_h)_{h∈{1,2,4,...}} be events
with arbitrary dependence. Suppose that, possibly conditional on a sigma-field H,
P(E_h | H) ≤ A_∗e^{−a_∗h} (h ≥ h_∗), where A_∗, a_∗, h_∗ > 0 are deterministic constants. For every
fixed c_∗ > 0 and 0 < η < a_∗/(2c_∗), E[exp(ηc_∗ ∑_h h 1[E_h]) | H] ≤ K_∗, (29) where K_∗ < ∞ depends
only on the displayed constants."

**Formalization Note.** `K` is chosen after `(A_∗, a_∗, h_∗, c_∗, η)` and before the probability
space, the σ-field and the events. Scales are `h = 2^e`. Conditional bounds given a sub-σ-field `H`
are written through their defining property: `P(E | H) ≤ c` a.s. iff `P(E ∩ G) ≤ c P(G)` for every
`G ∈ H`, and likewise `E[Y | H] ≤ K` a.s. for `Y ≥ 0` iff `∫_G Y ≤ K P(G)`; `H = ⊥` is the
unconditional case. The conclusion is stated for every finite truncation `∑_{e < E₀}` with `K`
independent of `E₀`, which by monotone convergence is (29) for the full (possibly infinite) sum. -/
theorem lemma_4_6 : ∀ (A a h c η : ℝ), 0 < A → 0 < a → 0 < h → 0 < c → 0 < η → η < a / (2 * c) →
    ∃ K : ℝ, ∀ (Ω : Type*) (mΩ : MeasurableSpace Ω) (μ : Measure Ω), IsProbabilityMeasure μ →
      ∀ (H : MeasurableSpace Ω), H ≤ mΩ → ∀ E : ℕ → Set Ω, (∀ e, MeasurableSet (E e)) →
        (∀ e : ℕ, h ≤ 2 ^ e → ∀ G, MeasurableSet[H] G →
          μ (E e ∩ G) ≤ ENNReal.ofReal (A * Real.exp (-(a * 2 ^ e))) * μ G) →
        ∀ (E₀ : ℕ) (G : Set Ω), MeasurableSet[H] G →
          ∫⁻ ω in G, ENNReal.ofReal (Real.exp (η * c *
              ∑ e ∈ Finset.range E₀, (2 : ℝ) ^ e * (E e).indicator (fun _ => (1 : ℝ)) ω)) ∂μ ≤
            ENNReal.ofReal K * μ G := by sorry

end RandOrderSort
