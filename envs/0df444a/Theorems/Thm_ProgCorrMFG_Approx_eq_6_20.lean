-- Prove2me | Theorems.Thm_ProgCorrMFG_Approx_eq_6_20
-- name    : ProgCorrMFG.Approx.eq_6_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:20:45.51109+00:00
-- url     : https://prove2.me/theorems/3c03b1af-b149-4613-90ea-01366d560a04
-- title:
--   (6.20), p. 21 — $\mathbb E_N[\mathrm{dist}_T(\mu^{1,N},\mu)]\to0$ in the coupling
-- statement:
--   Assume the hypotheses of Theorem 6.2, with (R2) witnessed by Borel maps $\alpha_t$. For each $N\ge2$, consider the coupling of pp. 20–21: i.i.d. initial states $X^j_0\sim\mathfrak m_0$, suggestions $\Phi_j(t,\cdot)=\alpha_t(Z_j,\mu^{(t+1)})$ with i.i.d. uniform seeds $Z_j$ independent of the flow $\mu\sim\rho_2$, and the states $X^{j,N}$ of (6.16), in which every player follows its suggestion. Let $\mu^{1,N}_t=\frac1{N-1}\sum_{k\ne1}\delta_{X^{k,N}_t}$. Then
--   $$\lim_{N\to\infty}\mathbb E_N\big[\mathrm{dist}_T(\mu^{1,N},\mu)\big]=0,\qquad\mathrm{dist}_T(\lambda,\lambda')=\sum_{t=0}^T\mathrm{dist}(\lambda_t,\lambda'_t).$$
--
--   The empirical measure of the other players tracks the random flow of the mean field solution: a law of large numbers conditional on the flow.
--
--   **Formalization Note** The limit runs along $N=n+2$ and holds for every sequence of couplings.
-- source:
--   Bonesini, Campi & Fischer, Correlated Equilibria for Mean Field Games with Progressive Strategies, arXiv:2212.01656v1, p. 21, (6.20)

import Mathlib
import Definitions.Def_ProgCorrMFG_Approx_Model
import Definitions.Def_ProgCorrMFG_Approx_NPlayer
import Definitions.Def_ProgCorrMFG_Approx_MFG
import Definitions.Def_ProgCorrMFG_Approx_Coupling

namespace ProgCorrMFG.Approx

open MeasureTheory ProbabilityTheory unitInterval Filter Topology

theorem eq_6_20 {T : ℕ} {X G : Type} [Fintype X] [DecidableEq X] [Nonempty X] [MeasurableSpace X]
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
    Tendsto (fun n => ∫ ω, distT (fun t => (empOthers ((C n).st ω t) 0).1) ((C n).flow ω) ∂(P n))
      atTop (𝓝 0) := by sorry

end ProgCorrMFG.Approx
