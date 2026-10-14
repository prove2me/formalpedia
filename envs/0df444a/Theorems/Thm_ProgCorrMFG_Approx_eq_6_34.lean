-- Prove2me | Theorems.Thm_ProgCorrMFG_Approx_eq_6_34
-- name    : ProgCorrMFG.Approx.eq_6_34
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:20:38.382696+00:00
-- url     : https://prove2.me/theorems/8ac6c099-8ac1-43c7-a9a8-8a4560552201
-- title:
--   (6.34), p. 24 — $\mathbb P_N(\tilde X^{1,N}_t\neq\bar X^{1,N}_t)\to0$
-- statement:
--   Assume the hypotheses of Theorem 6.2, with (R2) witnessed by Borel maps $\alpha_t$, and consider the coupling of pp. 20–21 for $N\ge2$, with an arbitrary deviation of player 1. Let $\tilde X^{1,N}$ be the state of the deviating player in the $N$-player system (6.17), and $\bar X^{1,N}$ the auxiliary process (6.19) that uses the same controls $\tilde u^{1,N}_t$ and noises but is driven by the true flow $\mu_t$ instead of the empirical measure $\tilde\mu^{1,N}_t$. Then for every $t\in[\![0,T]\!]$,
--   $$\lim_{N\to\infty}\mathbb P_N\big(\tilde X^{1,N}_t\neq\bar X^{1,N}_t\big)=0.$$
--
--   The deviating player's $N$-player trajectory becomes indistinguishable from a trajectory in the mean field game with the same controls, which is what lets the deviation be compared with the mean field optimum.
--
--   **Formalization Note** The limit runs along $N=n+2$, for every sequence of couplings; probabilities are in $[0,\infty]$.
-- source:
--   Bonesini, Campi & Fischer, Correlated Equilibria for Mean Field Games with Progressive Strategies, arXiv:2212.01656v1, p. 24, (6.34)

import Mathlib
import Definitions.Def_ProgCorrMFG_Approx_Model
import Definitions.Def_ProgCorrMFG_Approx_NPlayer
import Definitions.Def_ProgCorrMFG_Approx_MFG
import Definitions.Def_ProgCorrMFG_Approx_Coupling

namespace ProgCorrMFG.Approx

open MeasureTheory ProbabilityTheory unitInterval Filter Topology

theorem eq_6_34 {T : ℕ} {X G : Type} [Fintype X] [DecidableEq X] [Nonempty X] [MeasurableSpace X]
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
    ∀ t : Fin (T + 1), Tendsto (fun n => P n {ω | (C n).stt ω t 0 ≠ (C n).stb ω t}) atTop (𝓝 0) := by sorry

end ProgCorrMFG.Approx
