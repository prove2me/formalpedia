-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P12_nonMarkovianity_global_continuity
-- name    : QAlgorithms.Papers.Independent.Bridge50.P12.nonMarkovianity_global_continuity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:32:59.635402+00:00
-- url     : https://prove2.me/theorems/a0ad96c6-76b8-4139-9bac-5790752e14f1
-- title:
--   Global piecewise continuity bound for relative entropy non-Markovianity
-- statement:
--   Let $\rho,\sigma$ be density operators on nonzero finite-dimensional systems $A\otimes B\otimes C$. Put $D=\dim(A\otimes B\otimes C)$ and $t=\|\rho-\sigma\|_1$. Let $\Delta$ be the extended-relative-entropy distance in bits to Markov density operators, defined by zero conditional mutual information. Both distances are finite, and
--
--   $$|\Delta(\rho)-\Delta(\sigma)|\le\begin{cases}2(t\log_2D+h_2(t)),&t\le2/3,\\(t/2)\log_2D+h_2(t/2)+\log_2D,&t>2/3.\end{cases}$$
--
--   Here $h_2$ is binary entropy in bits. The first branch includes the boundary, so the selected entropy argument always lies in $[0,1]$. This removes the small-distance assumption of S21.
-- source:
--   Asymptotically Consistent Measures of General Quantum Resources: Discord, Non-Markovianity, and Non-Gaussianity, arXiv:2103.05665v4, PDF p. 21, Remark 5: global piecewise Markov continuity bound

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P12

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Bridge50.P12

open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntropyBits)

/-- PDF p.21, Remark 5, S129: the global piecewise bound without S112. -/
theorem nonMarkovianity_global_continuity {A B C : Type}
    [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [Nonempty A] [Nonempty B] [Nonempty C]
    (rho sigma : Matrix (A × (B × C)) (A × (B × C)) ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    normalizedResourceDistance markovStates rho ≠ ⊤ ∧ normalizedResourceDistance markovStates sigma ≠ ⊤ ∧
    |(normalizedResourceDistance markovStates rho).toReal - (normalizedResourceDistance markovStates sigma).toReal| ≤
      markovModulus (Fintype.card (A × (B × C))) (traceNorm (rho - sigma)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P12

end
