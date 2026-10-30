-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P12_nonMarkovianity_continuity
-- name    : QAlgorithms.Papers.Independent.Bridge50.P12.nonMarkovianity_continuity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:32:21.162596+00:00
-- url     : https://prove2.me/theorems/4a1a4bd2-d53f-445a-8a90-2225d58ce860
-- title:
--   Continuity of relative entropy non-Markovianity at small trace distance
-- statement:
--   Let $A,B,C$ be nonzero finite-dimensional systems and let $\rho,\sigma$ be density operators on $A\otimes B\otimes C$. Set $D=\dim(A\otimes B\otimes C)$ and $t=\|\rho-\sigma\|_1$. Define $\Delta$ as the infimum of extended relative entropy in bits over all Markov density operators, where Markov means $I(A:C\mid B)=H(AB)+H(BC)-H(B)-H(ABC)=0$. Singular reference states are included. If $t/2\le1/3$, then $\Delta(\rho),\Delta(\sigma)$ are finite and
--
--   $$|\Delta(\rho)-\Delta(\sigma)|\le2\bigl(t\log_2D+h_2(t)\bigr).$$
--
--   This gives the source's quantitative asymptotic-continuity estimate for a nonconvex free-state set.
-- source:
--   Asymptotically Consistent Measures of General Quantum Resources: Discord, Non-Markovianity, and Non-Gaussianity, arXiv:2103.05665v4, PDF p. 20, Theorem S21

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P12

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Bridge50.P12

open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntropyBits)

/-- PDF pp.20–21, Theorem S21, S112–S113: the premise uses t/2≤1/3,
whereas the entropy in the conclusion is h₂(t). -/
theorem nonMarkovianity_continuity {A B C : Type}
    [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [Nonempty A] [Nonempty B] [Nonempty C]
    (rho sigma : Matrix (A × (B × C)) (A × (B × C)) ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hdist : traceNorm (rho - sigma) / 2 ≤ 1 / 3) :
    normalizedResourceDistance markovStates rho ≠ ⊤ ∧ normalizedResourceDistance markovStates sigma ≠ ⊤ ∧
    |(normalizedResourceDistance markovStates rho).toReal - (normalizedResourceDistance markovStates sigma).toReal| ≤
      2 * (traceNorm (rho - sigma) * Real.logb 2 (Fintype.card (A × (B × C))) +
        binEntropy2 (traceNorm (rho - sigma))) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P12

end
