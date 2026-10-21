-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P27_meanEnergyIncrease
-- name    : QAlgorithms.Papers.Independent.Next46.P27.meanEnergyIncrease
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:22:52.108838+00:00
-- url     : https://prove2.me/theorems/eaf5b857-4ee1-4621-97ae-46a5fbf3a91c
-- title:
--   Zero-mean mean-energy increment
-- statement:
--   Let $\rho$ be a density on the full Fock space with finite photon-number mean $E(\rho)=\sum_{j\ge0}j\langle j|\rho|j\rangle$. Assume its annihilation first-moment series is convergent and $\operatorname{tr}(a\rho)=0$. For $\gamma>0$ let $\rho_t=\Phi_{\gamma t}(\rho)$, with $\Phi$ the exact Gaussian displacement channel. There exist $C>0$ and $\delta>0$ such that, for every $0<t<\delta$, $\rho_t$ has finite mean energy and
--
--   $$|E(\rho_t)-E(\rho)-\gamma t|\le C(\gamma t)^2.$$
--
--   Thus the first-order mean-energy increase is $\gamma t$, independently of the zero-mean input density. This retains the remainder strength in Eq.(4).
-- source:
--   The bosonic minimum output entropy conjecture and Lagrangian minimization, arXiv:0906.2758v3, PDF p. 2, Section II, Eq.(4): mean energy increment

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P27

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P27

open Filter MeasureTheory

open scoped Topology ENNReal ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

-- Mathlib deliberately leaves the general C*-algebra calculus opt-in.

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

/-- PDF p.2, Eq.(4): first-order mean-energy increment for zero-mean inputs.
The exact Eq.(1) channel defines the small-time evolution; no Euler map is used. -/
theorem meanEnergyIncrease (gamma : ℝ) (hgamma : 0 < gamma)
    (rho : B.FockOperator) (hrho : B.IsDensity rho) (henergy : A.FiniteEnergy rho)
    (hmean : Summable (fun j : ℕ => (Real.sqrt (j + 1 : ℝ) : ℂ) *
      rho (B.fockKet j) (j + 1))) (hzero : A.meanA rho = 0) :
    ∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ ∀ t : ℝ, 0 < t → t < delta →
      A.FiniteEnergy (A.displacementNoiseChannel (gamma * t) rho) ∧
      |B.photonMean (A.displacementNoiseChannel (gamma * t) rho) - B.photonMean rho - gamma * t| ≤
        C * (gamma * t) ^ 2 := by sorry

end QAlgorithms.Papers.Independent.Next46.P27

end
