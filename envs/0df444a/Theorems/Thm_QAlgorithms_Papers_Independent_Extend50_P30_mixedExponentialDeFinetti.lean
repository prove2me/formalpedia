-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P30_mixedExponentialDeFinetti
-- name    : QAlgorithms.Papers.Independent.Extend50.P30.mixedExponentialDeFinetti
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:28:57.719831+00:00
-- url     : https://prove2.me/theorems/6526a2ff-0c4f-40c0-9267-533f5ac285c1
-- title:
--   Mixed-state exponential stabilizer de Finetti theorem
-- statement:
--   Let $d$ be prime and let $\rho$ be a positive semidefinite trace-one state on $t\geq1$ blocks of $n$ qudits. Assume it commutes with all $R(O)$ for $O\in O_t(d)$. For $1\leq s\leq t$, there is a probability distribution on mixed stabilizer states, meaning maximally mixed code states, with the approximation below. Support on the symmetric subspace is not required.
--
--   $$
--   \frac12\left\|\rho_{1\ldots s}-\sum_\sigma p(\sigma)\sigma^{\otimes s}\right\|_1\leq2d^{(2n+2)^2/2}d^{-(t-s)/2}.
--   $$
--
--   This gives the source's mixed-state exponential stabilizer de finetti theorem in the fixed computational-basis and phase conventions.
--
--   **Formalization Note** Pure states carry norm one; stabilizer averages use density matrices to discard global phases. All finite tensor indices are explicitly ordered by copy, then physical qudit.
-- source:
--   Schur-Weyl Duality for the Clifford Group with Applications: Property Testing, a Robust Hudson Theorem, and de Finetti Representations, arXiv:1712.08628v3, PDF p. 58, theorem-7.6

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P30

noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Extend50.P30

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Gap20.P06 (ketBra)

attribute [local instance] Classical.propDecidable

/-- PDF p.58, Theorem 7.6: density commutation; mixtures are of maximally mixed code states. -/
theorem mixedExponentialDeFinetti (d n t s : ℕ) [NeZero d] [Fact (Nat.Prime d)]
    (ht : 1 ≤ t) (hs : 1 ≤ s) (hst : s ≤ t)
    (rho : Matrix (QuditCopies d n t) (QuditCopies d n t) ℂ) (hrho : QAlgorithms.IsDensityMatrix rho)
    (hinv : ∀ O : StochasticOrthogonal d t,
      rho * tensorRelation n (graphRelation O.val) = tensorRelation n (graphRelation O.val) * rho) :
    ∃ p : QuditOperator d n → ℝ, IsDistributionOn (mixedStabilizers d n) p ∧
      QAlgorithms.traceNorm (copyPrefixReduction s hst rho - stabilizerMixture s (mixedStabilizers d n) p) / 2 ≤
        2 * Real.rpow (d : ℝ) ((2 * (n : ℝ) + 2) ^ 2 / 2) *
          Real.rpow (d : ℝ) (-((t - s : ℕ) : ℝ) / 2) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P30

end
