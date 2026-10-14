-- Prove2me | Theorems.Thm_ProgCorrMFG_Approx_remark_6_3
-- name    : ProgCorrMFG.Approx.remark_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:20:24.973919+00:00
-- url     : https://prove2.me/theorems/dff7a128-a5ff-4d71-a2d3-a25920cb0282
-- title:
--   Remark 6.3, p. 15 — suggestions built from i.i.d. seeds have law $\gamma^N$
-- statement:
--   Let $\rho\in\mathcal P(\mathcal R\times\mathcal P(\mathcal X)^{T+1})$ satisfy (R2) with Borel maps $\alpha_t:[0,1]\times\mathcal P(\mathcal X)^{t+2}\to\mathcal E$, so that $\rho$ is the law of $((\alpha_t(Z,\mu^{(t+1)}))_t,\mu)$ for $Z\sim\nu$ independent of $\mu\sim\rho_2$. Let $\rho_1$ be a probability kernel with $\rho(d\varphi,dm)=\rho_1(d\varphi|m)\rho_2(dm)$. Let $Z_1,\dots,Z_N$ be i.i.d. uniform on $[0,1]$ and independent of a flow $\mu\sim\rho_2$, and set
--   $$\Phi_j(t,\cdot)=\alpha_t\big(Z_j,\mu^{(t+1)}\big)(\cdot),\qquad j\in[\![1,N]\!],\ t\in[\![0,T-1]\!].$$
--   Then
--   $$\mathbb P\circ(\Phi_1,\dots,\Phi_N)^{-1}=\gamma^N=\int_{\mathcal P(\mathcal X)^{T+1}}\prod_{j=1}^N\rho_1(\cdot|m)\,\rho_2(dm).$$
--
--   The remark identifies the correlated suggestion of Theorem 6.2 with the law of $N$ conditionally independent copies of the mean field suggestion, which is how the proof builds its $N$-player realizations.
-- source:
--   Bonesini, Campi & Fischer, Correlated Equilibria for Mean Field Games with Progressive Strategies, arXiv:2212.01656v1, p. 15, Remark 6.3

import Mathlib
import Definitions.Def_ProgCorrMFG_Approx_Model
import Definitions.Def_ProgCorrMFG_Approx_NPlayer
import Definitions.Def_ProgCorrMFG_Approx_MFG

namespace ProgCorrMFG.Approx

open MeasureTheory ProbabilityTheory unitInterval Filter Topology

theorem remark_6_3 {T : ℕ} {X G : Type} [Fintype X] [DecidableEq X] [Nonempty X] [MeasurableSpace X]
    [DiscreteMeasurableSpace X] [Fintype G] [Nonempty G] [MeasurableSpace G]
    [DiscreteMeasurableSpace G]
    (ρ : Measure (Strat T X G × Flow T X)) [IsProbabilityMeasure ρ]
    (α : (t : Fin T) → I → (Fin (t.1 + 2) → Meas X) → (X → G))
    (hα_meas : ∀ t, Measurable (fun p : I × (Fin (t.1 + 2) → Meas X) => α t p.1 p.2))
    (hα : ρ = ((volume : Measure I).prod (ρ.map Prod.snd)).map
      (fun p : I × Flow T X => ((fun t => α t p.1 (histSucc p.2 t)), p.2)))
    (ρ₁ : Kernel (Flow T X) (Strat T X G)) [IsMarkovKernel ρ₁]
    (hρ₁ : ρ = ((ρ.map Prod.snd) ⊗ₘ ρ₁).map Prod.swap)
    (N : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → Fin N → I) (μ : Ω → Flow T X) (hZ : Measurable Z) (hμ : Measurable μ)
    (hlaw : P.map (fun ω => (Z ω, μ ω)) =
      (Measure.pi fun _ : Fin N => (volume : Measure I)).prod (ρ.map Prod.snd)) :
    P.map (fun ω j => (fun t => α t (Z ω j) (histSucc (μ ω) t) : Strat T X G)) =
      gammaN (ρ.map Prod.snd) ρ₁ N := by sorry

end ProgCorrMFG.Approx
