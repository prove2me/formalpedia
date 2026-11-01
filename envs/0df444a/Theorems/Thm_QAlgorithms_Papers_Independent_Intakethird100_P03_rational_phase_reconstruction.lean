-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P03_rational_phase_reconstruction
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P03.rational_phase_reconstruction
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:00:48.275012+00:00
-- url     : https://prove2.me/theorems/d9ccbda2-11f8-4582-af1b-2d44c2716e64
-- title:
--   §3: exact recovery of a permutation eigenphase
-- statement:
--   Let $0\le\phi<1$ be rational with denominator at most $2^n$, and suppose a measurement returns the dyadic code $\phi'=u/2^{2n+1}$ with $0\le u<2^{2n+1}$. If its circular distance from $\phi$ satisfies
--
--   $$
--   d_{\mathbb R/\mathbb Z}(\phi',\phi)\le 2^{-2n-1},
--   $$
--
--   then $\phi$ is the unique normalized rational phase of denominator at most $2^n$ within that distance. One classical polynomial-time procedure, chosen before $n,u,\phi$, maps the full $2n+1$-bit dyadic word to the exact numerator/denominator encoding of $\phi$.
--
--   The zero phase is included, and the dyadic numerator need not be coprime to its denominator. The fixed-width input has length $O(n+1)$, so polynomial-time reconstruction has the source's bit-cost meaning.
-- source:
--   Quantum measurements and the Abelian Stabilizer Problem, arXiv:quant-ph/9511026v1, PDF p. 18, §3: exact recovery of a permutation eigenphase

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P03

noncomputable section

open scoped Matrix ComplexConjugate Kronecker

namespace QAlgorithms.Papers.Independent.Intakethird100.P03

open QAlgorithms.Papers.Independent.Renew46.P01 (cleanVector)

attribute [local instance] Classical.propDecidable

/-- PDF p.18: unique exact rational recovery from a 2n+1-bit dyadic measurement within
2^(-2n-1) on the phase circle, in polynomial time. The zero phase is included. -/
theorem rational_phase_reconstruction :
    ∃ recover : List Bool → List Bool, QAlgorithms.Complexity.PolyTimeComputable recover ∧
      ∀ (n numerator : ℕ), numerator < 2 ^ (2 * n + 1) →
      ∀ phi : ℚ, 0 ≤ phi → phi < 1 → phi.den ≤ 2 ^ n →
      phaseDistance ((numerator : ℝ) / (2 : ℝ) ^ (2 * n + 1)) (phi : ℝ) ≤
        1 / (2 : ℝ) ^ (2 * n + 1) →
      recover (rationalRecoveryInput n numerator) = encodeRational phi ∧
      ∀ psi : ℚ, 0 ≤ psi → psi < 1 → psi.den ≤ 2 ^ n →
        phaseDistance ((numerator : ℝ) / (2 : ℝ) ^ (2 * n + 1)) (psi : ℝ) ≤
          1 / (2 : ℝ) ^ (2 * n + 1) → psi = phi := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P03

end
