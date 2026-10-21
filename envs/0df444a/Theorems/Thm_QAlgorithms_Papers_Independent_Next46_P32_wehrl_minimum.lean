-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P32_wehrl_minimum
-- name    : QAlgorithms.Papers.Independent.Next46.P32.wehrl_minimum
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:33:19.209415+00:00
-- url     : https://prove2.me/theorems/e8cfbc4f-4a9c-48b8-9a25-eb7ee0a3da85
-- title:
--   Thermal attainment of the Wehrl output-entropy minimum
-- statement:
--   Let $n\ge1$, $0\le\eta\le1$ and $K\ge0$. The input ports are independent, the $a$ port is in $n$-mode vacuum, and the $b$ port may be any full-Fock density, including intermode correlations. With normalized coherent kets, define the Husimi density relative to ordinary Lebesgue measure and the shifted Wehrl entropy by
--
--   $$
--   Q_\rho(\mu)=\pi^{-n}\langle\mu|\rho|\mu\rangle,\qquad
--   W(\rho)=-\int Q_\rho(\mu)\ln(\pi^nQ_\rho(\mu))\,d^{2n}\mu.
--   $$
--
--   This entropy takes values in $[0,+\infty]$. If $W(\rho_b)=n(1+\ln(K+1))$, then the output $c=\sqrt\eta\,a+\sqrt{1-\eta}\,b$ satisfies
--
--   $$
--   W(\rho_c)\ge n\bigl(1+\ln(1+(1-\eta)K)\bigr).
--   $$
--
--   The product of $n$ identical thermal states of mean $K$ has exactly the required input entropy and attains equality at the output. This minimum is proved in the appendix and needs no conjecture hypothesis. The actual channel endpoints and the vacuum thermal state at $K=0$ are included.
-- source:
--   Classical capacity of bosonic broadcast communication and a new minimum output entropy conjecture, arXiv:0706.3416v1, PDF p. 8, Appendix A.1, Strong Conjecture 2: Wehrl, PDF pp.8-9

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P32

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P32

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity productCoeff)

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Dependency50.P39 (coherentCoefficient)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Appendix A.1, PDF pp.8-9: proved Wehrl minimum, with thermal attainment.
The typo referring to (A8) as the desired output lower bound means (A10).
Endpoints use the actual channel; the entropy definition has no scaling divisor. -/
theorem wehrl_minimum (n : ℕ) (hn : 0 < n) (eta K : ℝ)
    (heta : 0 ≤ eta) (heta1 : eta ≤ 1) (hK : 0 ≤ K) :
    wehrl (identicalThermalKernel n K) = ENNReal.ofReal ((n : ℝ) * (1 + Real.log (K + 1))) ∧
    wehrl (mixedOutput n eta (vacuum n) (identicalThermalKernel n K)) =
      ENNReal.ofReal ((n : ℝ) * (1 + Real.log ((1 - eta) * K + 1))) ∧
    ∀ rho : State (NumberString n),
      wehrl rho.coefficients = ENNReal.ofReal ((n : ℝ) * (1 + Real.log (K + 1))) →
      ENNReal.ofReal ((n : ℝ) * (1 + Real.log ((1 - eta) * K + 1))) ≤
        wehrl (mixedOutput n eta (vacuum n) rho.coefficients) := by sorry

end QAlgorithms.Papers.Independent.Next46.P32

end
