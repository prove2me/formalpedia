-- Prove2me | Theorems.Thm_ProgCorrMFG_Approx_claim_6_4
-- name    : ProgCorrMFG.Approx.claim_6_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:20:22.399864+00:00
-- url     : https://prove2.me/theorems/861042b8-eb36-4414-9e73-cee0b9b41b05
-- title:
--   Claim 6.4, p. 21 — $\mathbb E[\mathrm{dist}_T(\lambda,\hat\mu^{1,N})]\to0$ for $\lambda=\tilde\mu^{j,N}$ and $\lambda=\mu^{j,N}$
-- statement:
--   Assume the hypotheses of Theorem 6.2, with (R2) witnessed by Borel maps $\alpha_t$, and consider the coupling of pp. 20–21 for $N\ge2$, with an arbitrary deviation of player 1. Let $\tilde\mu^{j,N}$ be the empirical measures of the other players under (6.17), where player 1 deviates, let $\mu^{j,N}$ be those under (6.16), where nobody deviates, and let $\hat\mu^{1,N}_t=\frac1{N-1}\sum_{k=2}^N\delta_{\hat X^{k,N}_t}$ be the empirical measure of the system (6.18) of players $2,\dots,N$ alone. Then for $\lambda=\tilde\mu^{j,N}$ and for $\lambda=\mu^{j,N}$,
--   $$\lim_{N\to\infty}\mathbb E\big[\mathrm{dist}_T(\lambda,\hat\mu^{1,N})\big]=0,$$
--   uniformly in the player $j\in[\![1,N]\!]$.
--
--   A single deviating player does not move the empirical measure seen by the others in the limit.
--
--   **Formalization Note** The quantity inside the limit is the maximum over $j$ of the expectation, which is the paper's uniform bound (6.23) and implies the claim for each fixed $j$. The limit runs along $N=n+2$, for every sequence of couplings.
-- source:
--   Bonesini, Campi & Fischer, Correlated Equilibria for Mean Field Games with Progressive Strategies, arXiv:2212.01656v1, p. 21, Claim 6.4, (6.21)

import Mathlib
import Definitions.Def_ProgCorrMFG_Approx_Model
import Definitions.Def_ProgCorrMFG_Approx_NPlayer
import Definitions.Def_ProgCorrMFG_Approx_MFG
import Definitions.Def_ProgCorrMFG_Approx_Coupling

namespace ProgCorrMFG.Approx

open MeasureTheory ProbabilityTheory unitInterval Filter Topology

theorem claim_6_4 {T : ℕ} {X G : Type} [Fintype X] [DecidableEq X] [Nonempty X] [MeasurableSpace X]
    [DiscreteMeasurableSpace X] [Fintype G] [Nonempty G] [MeasurableSpace G]
    [DiscreteMeasurableSpace G]
    (M : Model T X G) (hΨ : M.PsiMeasurable) (hA1 : M.A1) (hA2 : M.A2) (hA3 : M.A3)
    (m₀ : Measure X) [IsProbabilityMeasure m₀]
    (ρ : Measure (Strat T X G × Flow T X)) [IsProbabilityMeasure ρ]
    (hsol : IsCorrelatedSolution M m₀ ρ) (hR1 : R1 ρ) (hR2 : R2 ρ)
    (α : (t : Fin T) → I → (Fin (t.1 + 2) → Meas X) → (X → G))
    (hα_meas : ∀ t, Measurable (fun p : I × (Fin (t.1 + 2) → Meas X) => α t p.1 p.2))
    (hα : ρ = ((volume : Measure I).prod (ρ.map Prod.snd)).map
      (fun p : I × Flow T X => ((fun t => α t p.1 (histSucc p.2 t)), p.2)))
    (Ω : ℕ → Type) [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)]
    (C : ∀ n, Coupling M m₀ (ρ.map Prod.snd) α (n + 2) (P n)) :
    Tendsto (fun n => Finset.univ.sup' Finset.univ_nonempty (fun j : Fin (n + 2) =>
        ∫ ω, distT (fun t => (empOthers ((C n).stt ω t) j).1)
          (fun t => (empOthers ((C n).sth ω t) 0).1) ∂(P n))) atTop (𝓝 0) ∧
    Tendsto (fun n => Finset.univ.sup' Finset.univ_nonempty (fun j : Fin (n + 2) =>
        ∫ ω, distT (fun t => (empOthers ((C n).st ω t) j).1)
          (fun t => (empOthers ((C n).sth ω t) 0).1) ∂(P n))) atTop (𝓝 0) := by sorry

end ProgCorrMFG.Approx
