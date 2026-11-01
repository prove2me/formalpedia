-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P09_hiding_resource_key_and_bell
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P09.hiding_resource_key_and_bell
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:39:56.836273+00:00
-- url     : https://prove2.me/theorems/3620e799-aecd-4536-9b0a-2a04db0c2670
-- title:
--   Proposition 1: positive-coefficient bound and near-unit distillable key
-- statement:
--   All states are normalized finite-dimensional bipartite density matrices. Gamma denotes transposition of Bob in the fixed product basis. The trace norm is the full trace norm. For a finite Bell expression S with real coefficients, C(S) and Q(S) are its largest signed classical value and its supremal signed quantum value over arbitrary finite local dimensions; Q_S(rho) optimizes complete local POVMs on the fixed state. For every integer m>=2, put d=m^2 and k=m. Let rho_m be the explicit Eq.(A.8) family at q=1/3: its even diagonal blocks are [q(tau_1+tau_2)/2]^tensor m, its off-diagonal even blocks are [q(tau_1-tau_2)/2]^tensor m, and its odd diagonal blocks are [(1/2-q)tau_2]^tensor m, divided by N_m=2q^m+2(1/2-q)^m. Here tau_1=[(rho_a+rho_s)/2]^tensor k and tau_2=rho_s^tensor k, with normalized antisymmetric and symmetric Werner states in dimension d. Specifically, rho_s=(I+F)/(d^2+d) and rho_a=(I-F)/(d^2-d), where F is the swap. Regroup all shields with their owners. These rho_m are densities and PPT, and
--
--   $$K_D(\rho_m^\Gamma\otimes\rho_m)\longrightarrow1\quad(m\to\infty).$$
--
--   For every nonnegative-coefficient Bell expression, the same family satisfies
--
--   $$Q_S(\rho_m\otimes\rho_m^\Gamma)\le C(S)+\frac{Q(S)}{2^{m-1}}.$$
--
--   K_D counts bits per copy of the paired resource. The construction is independent of S. The Bell domain is explicitly corrected; this illustrates almost one bit of distillable key with vanishing Bell excess.
-- source:
--   Bounds on quantum nonlocality via partial transposition, arXiv:1407.6999v3, PDF p. 3, Proposition 1: positive-coefficient bound and near-unit distillable key

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P09

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P09

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Filter

open QAlgorithms.Entanglement (IsSeparableDensity)

open QAlgorithms.Papers.Independent.Dependency50.P24
  (transposeSecond partyCut xForm swapPrivate hidingOne hidingTwo)

open QAlgorithms.Papers.Independent.Dependency50.P42 (dimensionedPower)

open QAlgorithms.Papers.Independent.Information100.P21 (Op FiniteLOCC)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Advance50.P47 (Box)

open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntanglement)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF pp.3,7, Proposition 1 and Eq.(A.8), CORRECTED Bell domain s>=0.
One computed PPT family independent of S; paired-resource distillable key tends to ONE bit. -/
theorem hiding_resource_key_and_bell :
    (∀ m : ℕ, 2 ≤ m → IsDensityMatrix (hidingResource m) ∧
      (transposeSecond (hidingResource m)).PosSemidef ∧
      ∀ (S : BellScenario) (s : BellCoefficients S), (∀ x y a b, 0 ≤ s x y a b) →
        stateValue s (paired (hidingResource m) (transposeSecond (hidingResource m))) ≤
          classicalBound s + quantumBound s / (2 : ℝ)^(m-1)) ∧
    Tendsto (fun j : ℕ => QAlgorithms.Papers.Independent.Gap48.P42.distillableKey
      (asFin (paired (transposeSecond (hidingResource (j+2))) (hidingResource (j+2)))))
      atTop (nhds 1) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P09

end
