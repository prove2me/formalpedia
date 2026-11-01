-- Prove2me | Theorems.Thm_ProcessingNetworks_MArP_theorem_D_25
-- name    : ProcessingNetworks.MArP.theorem_D_25
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:31:20.255987+00:00
-- url     : https://prove2.me/theorems/a4838883-642c-42c7-9924-680b14fb5ec8
-- title:
--   Theorem D.25 — strong law of large numbers for an irreducible CTMC
-- statement:
--   Let $X$ be an irreducible continuous-time Markov chain with regular generator matrix $\Lambda$ and initial distribution $\rho$. Then
--   $$
--   \mathbb P\Big\{\lim_{t\to\infty}\frac1t\int_0^t1_{\{X(s)=i\}}\,ds=\frac{1}{\mathbb E_i(T_i)\lambda(i)}\ \text{ for all } i\in\mathcal S\Big\}=1,
--   $$
--   where $T_i$ is the first passage time of $X$ to state $i$, the right side being $0$ when $\mathbb E_i(T_i)=\infty$. Moreover, when $X$ is positive recurrent with stationary distribution $\pi$, one has for any bounded function $f:\mathcal S\to\mathbb R$,
--   $$
--   \mathbb P\Big\{\lim_{t\to\infty}\frac1t\int_0^tf(X(s))\,ds=\bar f\Big\}=1,\qquad \bar f=\sum_{j\in\mathcal S}\pi(j)f(j).
--   $$
--
--   The first statement gives the long-run fraction of time in each state for every irreducible chain, recurrent or not. It is the source of the occupation-time limit (E.10) for a Markovian arrival process.
--
--   **Formalization Note** $\mathbb E_i(T_i)$ is the published `meanReturnTime`, a value in $[0,\infty]$, and the inverse of $\infty$ is $0$. Positive recurrence and stationarity are the published `PositiveRecurrent` and `IsStationaryDistribution`.
--
--   Differences from the source:
--   - encoding: $\Lambda$ regular (Definition D.3) → `IsGenerator Λ` and `hnonexp`, $\sigma_n\to\infty$ almost surely for this chain; reason: under irreducibility, non-explosion from one initial law is equivalent to Definition D.2.
--   - encoding: a CTMC (Definition D.6) → a process constructed from jump chain and clocks, `IsJumpHoldCTMC`; reason: the book states that without loss of generality every CTMC is so constructed (p.290).
--   - encoding: $\mathbb P\{\cdots\}=1$ → `∀ᵐ ω`; reason: the complement of the event is null, which is the same statement for a measurable event.
-- source:
--   Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Theorem D.25, p.296 (PDF p.312)

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_StabilityConditions
import Definitions.Def_ProcessingNetworks_MArP_IsJumpHoldCTMC
import Definitions.Def_ProcessingNetworks_MArP_occupationTime

open MeasureTheory ProbabilityTheory Filter

namespace ProcessingNetworks.MArP

/-- Theorem D.25 (Dai & Harrison, Processing Networks, pre-publication draft 2020-4-2, p.296,
PDF p.312). Let `X` be an irreducible CTMC with regular generator `Λ` and initial distribution `ρ`.
Then `P{lim_{t→∞} (1/t) ∫₀ᵗ 1{X(s) = i} ds = 1 / (E_i(T_i) λ(i)) for all i ∈ S} = 1`. Moreover, when
`X` is positive recurrent with stationary distribution `π`, for any bounded `f : S → ℝ`,
`P{lim_{t→∞} (1/t) ∫₀ᵗ f(X(s)) ds = ∑_j π(j) f(j)} = 1`.

**Formalization Note.** Regularity of `Λ` is `hΛ` (Definition D.1 with (D.2)) together with
`hnonexp`, which says that this chain does not explode. For an irreducible `Λ` that is equivalent to
Definition D.2. `E_i(T_i)` is `meanReturnTime` in `ℝ≥0∞`, positive and possibly `⊤`; the inverse of
`⊤` is `0`, which is the book's value `1 / (∞ · λ(i)) = 0` for a chain that is not positive
recurrent. "For all `i`" is inside the almost-sure event. Integrands are integrable on almost every
path because they are piecewise constant with finitely many pieces on `[0, t]`. -/
theorem theorem_D_25 {S Ω : Type*} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {Λ : S → S → ℝ} (hΛ : IsGenerator Λ) (ρ : PMF S)
    {Y : ℕ → Ω → S} {τ : ℕ → Ω → ℝ} {X : ℝ → Ω → S} (hX : IsJumpHoldCTMC hΛ ρ Y τ X)
    (hnonexp : ∀ᵐ ω, Tendsto
      (fun n => ProcessingNetworks.Stability.jumpTime (exitRate Λ) Y τ n ω) atTop atTop)
    (hirr : ProcessingNetworks.Stability.Irreducible (jumpMatrix hΛ)) :
    (∀ᵐ ω, ∀ i, Tendsto (fun t : ℝ => (1 / t) * occupationTime X i t ω) atTop
      (nhds ((ProcessingNetworks.Stability.meanReturnTime (jumpMatrix hΛ) (exitRate Λ) i *
        ENNReal.ofReal (exitRate Λ i))⁻¹).toReal)) ∧
    (ProcessingNetworks.Stability.PositiveRecurrent (jumpMatrix hΛ) (exitRate Λ) →
      ∀ π : PMF S,
        ProcessingNetworks.Stability.IsStationaryDistribution (jumpMatrix hΛ) (exitRate Λ) π →
      ∀ f : S → ℝ, (∃ C, ∀ i, |f i| ≤ C) →
        ∀ᵐ ω, Tendsto (fun t : ℝ => (1 / t) * ∫ u in (0 : ℝ)..t, f (X u ω)) atTop
          (nhds (∑' j, (π j).toReal * f j))) := by sorry

end ProcessingNetworks.MArP
