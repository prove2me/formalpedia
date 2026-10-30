-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P46_entropy_static_lipschitz
-- name    : QAlgorithms.Papers.Independent.Advance50.P46.entropy_static_lipschitz
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:13:04.163349+00:00
-- url     : https://prove2.me/theorems/371efb3f-f093-43ce-ae93-dcb72375cb9b
-- title:
--   Proposition 7.2, static entropy Lipschitz estimates
-- statement:
--   Let $\rho,\sigma$ be normalized positive trace-class states on an infinite-dimensional separable complex Hilbert space, and let $q>1$. Define $T_q(\rho)=(1-\operatorname{Tr}\rho^q)/(q-1)$ and use the source convention $S_q(\rho)=\log(\operatorname{Tr}\rho^q)/(q-1)$. Then
--
--   $$|T_q(\rho)-T_q(\sigma)|\le\frac q{q-1}\|\rho-\sigma\|_q\le\frac q{q-1}\|\rho-\sigma\|_1.$$
--
--   If $\delta>0$, $\|\rho\|_q\ge\delta$, and $\|\rho-\sigma\|_q\le\varepsilon<\delta$, then
--
--   $$|S_q(\rho)-S_q(\sigma)|\le\frac q{(q-1)(\delta-\varepsilon)}\|\rho-\sigma\|_q\le\frac q{(q-1)(\delta-\varepsilon)}\|\rho-\sigma\|_1.$$
--
--   These static continuity estimates require no Hamiltonian or energy hypothesis. The sign of $S_q$ follows Definition 7.1, rather than the more usual Renyi entropy convention.
-- source:
--   Convergence rates for quantum evolution & entropic continuity bounds in infinite dimensions, arXiv:1810.00863v3, PDF p. 35, Proposition 7.2, static entropy Lipschitz estimates

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P46

noncomputable section

open MeasureTheory Filter

open scoped ENNReal NNReal Topology BigOperators Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Advance50.P46

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Bridge50.P23 (energyMagnitude numberEnergy)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsTraceClass traceSize rankOne tensorApply productCoeff IsBarycenter)

attribute [local instance] Classical.propDecidable Classical.decEq

export QAlgorithms.Papers.Independent.Claimed50.P39 (g)

/-- Proposition 7.2, PDF pp.35--36: both Schatten-to-trace norm chains, with
q>1 inherited from Definition 7.1. The redundant alpha is absent because no
quantity in the static statement depends on it. -/
theorem entropy_static_lipschitz {I : Type} [Countable I] [Infinite I]
    (rho sigma : State I) (q : ℝ) (hq : 1 < q) :
    (|tsallisEntropy q rho - tsallisEntropy q sigma| ≤
      q / (q - 1) * traceClassSchattenQNorm q (rho.coefficients - sigma.coefficients) ∧
      q / (q - 1) * traceClassSchattenQNorm q (rho.coefficients - sigma.coefficients) ≤
        q / (q - 1) * (traceSize (rho.coefficients - sigma.coefficients)).toReal) ∧
    (∀ delta epsilon : ℝ, 0 < delta → delta ≤ traceClassSchattenQNorm q rho.coefficients →
      traceClassSchattenQNorm q (rho.coefficients - sigma.coefficients) ≤ epsilon → epsilon < delta →
      |signedRenyiEntropy q rho - signedRenyiEntropy q sigma| ≤
        q / ((q - 1) * (delta - epsilon)) *
          traceClassSchattenQNorm q (rho.coefficients - sigma.coefficients) ∧
      q / ((q - 1) * (delta - epsilon)) *
          traceClassSchattenQNorm q (rho.coefficients - sigma.coefficients) ≤
        q / ((q - 1) * (delta - epsilon)) *
          (traceSize (rho.coefficients - sigma.coefficients)).toReal) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P46

end
