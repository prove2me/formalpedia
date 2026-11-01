-- Prove2me | Theorems.Thm_ProcessingNetworks_MArP_corollary_C_22
-- name    : ProcessingNetworks.MArP.corollary_C_22
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:29:20.585117+00:00
-- url     : https://prove2.me/theorems/48ec08dc-a622-448d-a9f8-908fc5698999
-- title:
--   Corollary C.22 — strong law for transition frequencies of a DTMC
-- statement:
--   Let $X$ be an irreducible, positive recurrent discrete-time Markov chain on a countable state space with transition matrix $P$ and stationary distribution $\pi$. For each $i,j\in\mathcal S$ and each initial distribution $\mu$,
--   $$
--   \mathbb P_\mu\Big\{\lim_{N\to\infty}\frac1N\sum_{k=0}^{N-1}1_{\{X_k=i,\ X_{k+1}=j\}}=\pi(i)P_{ij}\Big\}=1 .
--   $$
--
--   The long-run frequency of the transition $i\to j$ is therefore $\pi(i)P_{ij}$. This is the discrete-time ingredient of the jump-count law for continuous-time chains.
--
--   Differences from the source:
--   - encoding: $\mathbb P_\mu\{\cdots\}=1$ → `∀ᵐ ω`; reason: the complement of the event is null, which is the same statement for a measurable event.
--   - encoding: the section's unique stationary distribution $\pi$ → any `π` with `IsInvariantDistribution P π`; reason: uniqueness is Theorem C.19 and there is one such `π`.
-- source:
--   Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Corollary C.22, eq. (C.15), p.280 (PDF p.296)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_MaxWeight_Chain
import Definitions.Def_ProcessingNetworks_MArP_IsInvariantDistribution
import Definitions.Def_ProcessingNetworks_MArP_IsDTMC

open MeasureTheory ProbabilityTheory Filter
open Classical

namespace ProcessingNetworks.MArP

/-- Corollary C.22, eq. (C.15) (Dai & Harrison, Processing Networks, pre-publication draft 2020-4-2,
p.280, PDF p.296). For an irreducible positive recurrent DTMC with stationary distribution `π`, for
each `i, j ∈ S` and each initial distribution `μ`,
`P_μ{lim_{N→∞} (1/N) ∑_{k=0}^{N-1} 1{X_k = i, X_{k+1} = j} = π(i) P_ij} = 1`.

**Formalization Note.** Irreducibility and positive recurrence are the standing assumptions of the
section ("In the rest of this section, we assume…", p.280). -/
theorem corollary_C_22 {S Ω : Type*} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (P : KellyStochasticNetworks.MaxWeight.Chain S)
    (hirr : KellyStochasticNetworks.MaxWeight.Irreducible P)
    (hpr : KellyStochasticNetworks.MaxWeight.PositiveRecurrent P)
    (π : PMF S) (hπ : IsInvariantDistribution P π)
    (i j : S) (μ : PMF S) (X : ℕ → Ω → S) (hX : IsDTMC P μ X) :
    ∀ᵐ ω, Tendsto
      (fun N : ℕ => (1 / (N : ℝ)) *
        ∑ k ∈ Finset.range N, if X k ω = i ∧ X (k + 1) ω = j then (1 : ℝ) else 0)
      atTop (nhds ((π i).toReal * (P i j).toReal)) := by sorry

end ProcessingNetworks.MArP
