-- Prove2me | Theorems.Thm_ProcessingNetworks_MArP_theorem_D_26
-- name    : ProcessingNetworks.MArP.theorem_D_26
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:31:11.42134+00:00
-- url     : https://prove2.me/theorems/a740e1d8-4495-4882-ba2a-3252701a4786
-- title:
--   Theorem D.26 — strong law for the jump counts of a CTMC
-- statement:
--   Let $X$ be a continuous-time Markov chain on a countable state space $\mathcal S$ with generator $\Lambda$, irreducible and positive recurrent with unique stationary distribution $\pi$. For $i\ne j$ let $J(i,j,t)$ be the number of jumps from state $i$ to state $j$ in $(0,t]$. Then
--   $$
--   \mathbb P_\mu\Big\{\lim_{t\to\infty}\frac1tJ(i,j,t)=\pi(i)\Lambda_{ij}\Big\}=1
--   $$
--   for each initial distribution $\mu$.
--
--   The stationary probability flow $\pi(i)\Lambda_{ij}$ is thus the almost-sure long-run rate of $i\to j$ transitions. For a Markovian arrival process this gives the rate of triggered arrivals, (E.12).
--
--   **Formalization Note** Theorem D.26 sits in Section D.7, whose opening assumes bounded transition rates (D.28); the Lean statement does not assume (D.28). No non-explosion hypothesis is needed: positive recurrence includes recurrence of the jump chain, which with irreducibility forces $\sigma_n\to\infty$ almost surely. The initial distribution is written $\rho$.
--
--   Differences from the source:
--   - generalization: the transition rates are bounded, $\sup_i\lambda(i)<\infty$ (D.28), the standing assumption of Section D.7 → no bound on the rates, only `IsGenerator Λ`; reason: renewal–reward over returns to $i$ gives the rate $G_{ij}/\mathbb E_i(T_i)=\pi(i)\Lambda_{ij}$ for any positive recurrent chain, and on generators satisfying (D.28) the statement is the book's.
--   - encoding: a CTMC (Definition D.6) → a process constructed from jump chain and clocks, `IsJumpHoldCTMC`; reason: the book states that without loss of generality every CTMC is so constructed (p.290).
--   - encoding: the unique stationary distribution $\pi$ → any `π` with `IsStationaryDistribution`; reason: uniqueness is Theorem D.17 and there is one such `π`.
--   - encoding: $\mathbb P_\mu\{\cdots\}=1$ → `∀ᵐ ω`; reason: the complement of the event is null, which is the same statement for a measurable event.
-- source:
--   Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Theorem D.26, eq. (D.32), p.297 (PDF p.313)

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_StabilityConditions
import Definitions.Def_ProcessingNetworks_MArP_IsJumpHoldCTMC
import Definitions.Def_ProcessingNetworks_MArP_jumpCount

open MeasureTheory ProbabilityTheory Filter

namespace ProcessingNetworks.MArP

/-- Theorem D.26, eq. (D.32) (Dai & Harrison, Processing Networks, pre-publication draft 2020-4-2,
p.297, PDF p.313). Let `X` be a CTMC on a countable state space, irreducible and positive recurrent
with unique stationary distribution `π`. For each `i ≠ j`, with `J(i, j, t)` the number of jumps from
`i` to `j` in `(0, t]`, `P_μ{lim_{t→∞} (1/t) J(i, j, t) = π(i) Λ_ij} = 1` for each initial
distribution `μ`.

**Formalization Note.** Theorem D.26 sits in Section D.7, whose opening assumes bounded transition
rates (D.28); the Lean statement does not assume (D.28), so it is a generalization (the limit
`G_ij / E_i(T_i) = π(i) Λ_ij` follows from renewal–reward over returns to `i`). No non-explosion
hypothesis is needed: positive recurrence includes recurrence of the jump chain, which with
irreducibility forces `σ_n → ∞` almost surely. The initial distribution is `ρ`. The uniqueness of `π`
is Theorem D.17, so `π` is any stationary distribution. -/
theorem theorem_D_26 {S Ω : Type*} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {Λ : S → S → ℝ} (hΛ : IsGenerator Λ) (ρ : PMF S)
    {Y : ℕ → Ω → S} {τ : ℕ → Ω → ℝ} {X : ℝ → Ω → S} (hX : IsJumpHoldCTMC hΛ ρ Y τ X)
    (hirr : ProcessingNetworks.Stability.Irreducible (jumpMatrix hΛ))
    (hpr : ProcessingNetworks.Stability.PositiveRecurrent (jumpMatrix hΛ) (exitRate Λ))
    (π : PMF S)
    (hπ : ProcessingNetworks.Stability.IsStationaryDistribution (jumpMatrix hΛ) (exitRate Λ) π)
    (i j : S) (hij : i ≠ j) :
    ∀ᵐ ω, Tendsto
      (fun t : ℝ => (1 / t) *
        (jumpCount Y (ProcessingNetworks.Stability.jumpTime (exitRate Λ) Y τ) i j t ω : ℝ))
      atTop (nhds ((π i).toReal * Λ i j)) := by sorry

end ProcessingNetworks.MArP
