-- Prove2me | Theorems.Thm_ProcessingNetworks_MArP_theorem_C_21
-- name    : ProcessingNetworks.MArP.theorem_C_21
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:30:07.928927+00:00
-- url     : https://prove2.me/theorems/6d858c88-9c7e-436c-9d65-c321ba3734f9
-- title:
--   Theorem C.21 — strong law of large numbers for a positive recurrent DTMC
-- statement:
--   Let $X$ be an irreducible, positive recurrent discrete-time Markov chain on a countable state space $\mathcal S$, with transition matrix $P$ and stationary distribution $\pi$; aperiodicity is not assumed. Let $f:\mathcal S\to\mathbb R$ be a function such that at least one of $\pi(f^+)$ and $\pi(f^-)$ is finite. Then for each initial distribution $\mu$,
--   $$
--   \mathbb P_\mu\Big\{\lim_{N\to\infty}\frac1N\sum_{k=0}^{N-1}f(X_k)=\pi(f)\Big\}=1 ,
--   $$
--   where $\pi(f)=\pi(f^+)-\pi(f^-)\in[-\infty,\infty]$.
--
--   This ergodic theorem is the discrete-time source of every long-run average in the book, and it applies to functions whose mean is infinite.
--
--   **Formalization Note** Positive recurrence and irreducibility are the published `KellyStochasticNetworks.MaxWeight` notions: every state has finite expected return time.
--
--   Differences from the source:
--   - encoding: $\mathbb P_\mu\{\cdots\}=1$ with a limit in $[-\infty,\infty]$ → `∀ᵐ ω` for convergence in `EReal`; reason: the complement of the event is null, which is the same statement for a measurable event, and `EReal` holds the book's infinite limits.
--   - encoding: the unique stationary distribution $\pi$ (Theorem C.19) → any `π` with `IsInvariantDistribution P π`; reason: existence and uniqueness are Theorem C.19, not part of Theorem C.21, and there is one such `π`.
-- source:
--   Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Theorem C.21, eq. (C.14), p.280 (PDF p.296)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_MaxWeight_Chain
import Definitions.Def_ProcessingNetworks_MArP_signedMean
import Definitions.Def_ProcessingNetworks_MArP_IsInvariantDistribution
import Definitions.Def_ProcessingNetworks_MArP_IsDTMC

open MeasureTheory ProbabilityTheory Filter

namespace ProcessingNetworks.MArP

/-- Theorem C.21 (SLLN for a DTMC), eq. (C.14) (Dai & Harrison, Processing Networks, pre-publication
draft 2020-4-2, p.280, PDF p.296). Let `X` be an irreducible positive recurrent DTMC on a countable
space with stationary distribution `π`, and `f : S → ℝ` with at least one of `π(f⁺)`, `π(f⁻)` finite.
For each initial distribution `μ`, `P_μ{lim_{N→∞} (1/N) ∑_{k=0}^{N-1} f(X_k) = π(f)} = 1`.

**Formalization Note.** The limit may be `±∞`, so the convergence is in `EReal`. Aperiodicity is not
assumed. The unique stationary distribution of the book is the bound `π`, with hypothesis `hπ`.
`∀ᵐ ω` says that the complement of the event is null. -/
theorem theorem_C_21 {S Ω : Type*} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (P : KellyStochasticNetworks.MaxWeight.Chain S)
    (hirr : KellyStochasticNetworks.MaxWeight.Irreducible P)
    (hpr : KellyStochasticNetworks.MaxWeight.PositiveRecurrent P)
    (π : PMF S) (hπ : IsInvariantDistribution P π)
    (f : S → ℝ) (hf : nonnegMean π f ≠ ⊤ ∨ nonnegMean π (fun i => -f i) ≠ ⊤)
    (μ : PMF S) (X : ℕ → Ω → S) (hX : IsDTMC P μ X) :
    ∀ᵐ ω, Tendsto
      (fun N : ℕ => (((1 / (N : ℝ)) * ∑ k ∈ Finset.range N, f (X k ω) : ℝ) : EReal))
      atTop (nhds (signedMean π f)) := by sorry

end ProcessingNetworks.MArP
