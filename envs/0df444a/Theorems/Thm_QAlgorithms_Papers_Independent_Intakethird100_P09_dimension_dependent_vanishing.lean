-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P09_dimension_dependent_vanishing
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P09.dimension_dependent_vanishing
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:44:36.108245+00:00
-- url     : https://prove2.me/theorems/d4842bfe-4a6f-4f19-b99d-dbfa7cf2987a
-- title:
--   Unnumbered after Eq. (21): dimension-dependent vanishing
-- statement:
--   All states are normalized finite-dimensional bipartite density matrices. Gamma denotes transposition of Bob in the fixed product basis. The trace norm is the full trace norm. For a finite Bell expression S with real coefficients, C(S) and Q(S) are its largest signed classical value and its supremal signed quantum value over arbitrary finite local dimensions; Q_S(rho) optimizes complete local POVMs on the fixed state.
--
--   The quantities R, T^infinity and R_H optimize arbitrary finite Bell scenarios and LOCC preprocessing of independent copies, using limsup per positive copy number. Input laws are arbitrary joint laws. T^infinity takes its innermost infimum over a one-copy separable sigma, comparing the same channel and the same measurements on rho^n and sigma^n. R_H counts the successful local-filter branch with its probability, after normalizing that branch; a zero-probability branch scores zero. E_r is the unregularized relative entropy of entanglement. All relative entropies and logarithms use bits and retain infinity on support failure. Let rho_j be PPT density matrices with total dimensions d_j tending to infinity. Suppose rho_j belongs to D(epsilon_j), 0<epsilon_j<1/2, and epsilon_j log_2(d_j) tends to zero. Here D(epsilon_j) requires a normalized separable same-space sigma_j with ||rho_j^Gamma-sigma_j^Gamma||_1<=epsilon_j. Then
--
--   $$R(\rho_j)\longrightarrow0,\qquad R_H(\rho_j)\longrightarrow0.$$
--
--   In addition, the explicit Eq.(9) states built from any sequence of flat unitaries of shield dimensions j+1 satisfy these two limits. The flat modulus uses the corrected 1/sqrt(j+1) normalization. This formalizes “faster than 1/log d” as a little-o condition, and includes the source’s example.
-- source:
--   Bounds on quantum nonlocality via partial transposition, arXiv:1407.6999v3, PDF p. 4, Unnumbered after Eq. (21): dimension-dependent vanishing

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

/-- PDF p.4, following Eq.(21): little-o condition epsilon log_2(total dimension)->0,
PPT and genuine near-SEP witnesses; both measures vanish. Includes the Eq.(9) example. -/
theorem dimension_dependent_vanishing :
    (∀ (a b : ℕ → ℕ+) (rho : (j : ℕ) → Op (Fin (a j) × Fin (b j))) (epsilon : ℕ → ℝ),
      (∀ j, (transposeSecond (rho j)).PosSemidef ∧ rho j ∈ nearSep (epsilon j) ∧
        0 < epsilon j ∧ epsilon j < 1/2) →
      Tendsto (fun j => ((a j : ℕ) * (b j : ℕ))) atTop atTop →
      Tendsto (fun j => epsilon j * (Real.log ((a j : ℝ) * (b j : ℝ)) / Real.log 2))
        atTop (nhds 0) →
      Tendsto (fun j => asymptoticR false (rho j)) atTop (nhds 0) ∧
      Tendsto (fun j => asymptoticRH false (rho j)) atTop (nhds 0)) ∧
    (∀ U : (j : ℕ) → Matrix.unitaryGroup (Fin (j+1)) ℂ,
      (∀ j i k, ‖(U j : Op (Fin (j+1))) i k‖ = (Real.sqrt (j+1 : ℝ))⁻¹) →
      Tendsto (fun j => asymptoticR false (asFin (pptPrivate ⟨j+1, by omega⟩ (U j))))
        atTop (nhds 0) ∧
      Tendsto (fun j => asymptoticRH false (asFin (pptPrivate ⟨j+1, by omega⟩ (U j))))
        atTop (nhds 0)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P09

end
