-- Prove2me | Theorems.Thm_ProcessingNetworks_MArP_proposition_E_7
-- name    : ProcessingNetworks.MArP.proposition_E_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:36:03.940981+00:00
-- url     : https://prove2.me/theorems/e357a58b-06c9-4673-9d27-bc9679de3c16
-- title:
--   Proposition E.7 — strong law and uniform integrability of a Markovian arrival process
-- statement:
--   Let $E=\{E(t),t\ge 0\}$ be a Markovian arrival process with arrivals-regulating Markov chain $Y$, and fix a constant $h\ge 0$. The chain $Y$ has a unique stationary distribution $\pi$, and:
--
--   1. the following strong law of large numbers holds:
--   $$
--   \mathbb P\Big\{\lim_{t\to\infty}\frac1tE(ht)=\lambda h\Big\}=1,
--   $$
--   where
--   $$
--   \lambda=\sum_{k=1}^r\delta^k\theta_k,\qquad
--   \theta_k=\sum_{s\in\mathcal S}\pi(s)\beta_k(s)+\sum_{s,\tilde s\in\mathcal S}\pi(s)\Lambda_{s\tilde s}\,q_k(s,\tilde s);
--   $$
--   2. the family of random variables $\big\{\frac1tE(th),\ t\ge 1\big\}$ is uniformly integrable.
--
--   The book cites part 1 at virtually every point where a MArP appears, and part 2 is what extends the fluid-limit stability theorem to networks with Markovian inputs.
--
--   **Formalization Note** The primitives are those of (E.1): the same Poisson process $\xi^k$ appears in each term of the sum over states. In part 2 a vector is measured by the norm $|x|=\sum_i|x_i|$ of the book's notation guide.
--
--   Differences from the source:
--   - reading: (E.6) prints $q(s,\tilde s)$ → $q_k(s,\tilde s)$; reason: $\theta_k$ counts type-$k$ batches, and the proof's (E.11)–(E.12) use $q_k$.
--   - encoding: "$\pi$ is the unique stationary distribution" → a first clause `∃! π, IsStationaryDistribution …`, and part 1 for every stationary `π`; reason: the same assertion, made explicit.
--   - encoding: $\mathbb P\{\cdots\}=1$ → `∀ᵐ ω` for one event on the whole vector in the product topology of `Fin I → ℝ`; reason: the complement of the event is null, which is the same statement for a measurable event.
--   - encoding: uniform integrability of the vector $\frac1tE(th)$ → uniform integrability of $\frac1t\sum_iE_i(th)$; reason: for $E\ge 0$ this sum is the book's norm $|\cdot|$.
-- source:
--   Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Proposition E.7, eqs. (E.4)–(E.7), pp.306–307 (PDF pp.322–323)

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_StabilityConditions
import Definitions.Def_ProcessingNetworks_MArP_IsUniformlyIntegrable
import Definitions.Def_ProcessingNetworks_MArP_arrivalProcess
import Definitions.Def_ProcessingNetworks_MArP_arrivalRate

open MeasureTheory ProbabilityTheory Filter

namespace ProcessingNetworks.MArP

/-- Proposition E.7 (Dai & Harrison, Processing Networks, pre-publication draft 2020-4-2,
pp.306–307, PDF pp.322–323). Let `E` be a MArP and fix `h ≥ 0`.
(a) `P{lim_{t→∞} (1/t) E(ht) = λh} = 1`, eq. (E.4), where `λ = ∑_k δᵏ θ_k`, eq. (E.5),
`θ_k = ∑_s π(s) β_k(s) + ∑_{s, s̃} π(s) Λ_{s s̃} q_k(s, s̃)`, eq. (E.6), and `π` is the unique stationary
distribution of the ARMC.
(b) The family `{(1/t) E(th), t ≥ 1}` is uniformly integrable, eq. (E.7).

**Formalization Note.** The first clause is the existence and uniqueness of `π` that (E.6) asserts.
The limit in (a) is one event for the whole vector, in the product topology of `Fin I → ℝ`. In (b) a
vector is measured by its ℓ¹ norm `∑_i E_i`, the book's `|·|` (the Guide, p.xv); since `E ≥ 0` this
sum is that norm, and for finite `I` uniform integrability of the norm is equivalent to that of each
component. -/
theorem proposition_E_7 {I d r : ℕ} (D : MArPData I d r) {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] (P : MArPPrimitives D Ω) (h : ℝ) (hh : 0 ≤ h) :
    (∃! π : PMF (Fin d), ProcessingNetworks.Stability.IsStationaryDistribution
      (jumpMatrix D.generator) (exitRate D.Λ) π) ∧
    (∀ π : PMF (Fin d), ProcessingNetworks.Stability.IsStationaryDistribution
        (jumpMatrix D.generator) (exitRate D.Λ) π →
      ∀ᵐ ω, Tendsto
        (fun t : ℝ => fun i => (1 / t) * (arrivalProcess P (h * t) ω i : ℝ))
        atTop (nhds (fun i => arrivalRate D π i * h))) ∧
    IsUniformlyIntegrable
      (fun (t : Set.Ici (1 : ℝ)) ω =>
        (1 / (t : ℝ)) * ∑ i, (arrivalProcess P ((t : ℝ) * h) ω i : ℝ)) := by sorry

end ProcessingNetworks.MArP
