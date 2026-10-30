-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P30_pureExponentialDeFinetti
-- name    : QAlgorithms.Papers.Independent.Extend50.P30.pureExponentialDeFinetti
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:26:21.915739+00:00
-- url     : https://prove2.me/theorems/2164e5fa-d187-42d1-b5ba-4ab8133c860e
-- title:
--   Pure-state exponential stabilizer de Finetti theorem
-- statement:
--   Let $d$ be prime, $t\geq1$, and let $\Psi$ be a normalized symmetric $t$-block pure state, each block consisting of $n$ qudits. Assume every graph unitary $R(O)$, $O\in O_t(d)$, fixes the vector itself. For $1\leq s\leq t$, a probability distribution $p$ on pure stabilizer density matrices approximates the first $s$ blocks in half the trace norm. No small-error assumption is imposed.
--
--   $$
--   \frac12\left\|\Psi_{1\ldots s}-\sum_Sp(S)S^{\otimes s}\right\|_1\leq2d^{(n+2)^2/2}d^{-(t-s)/2}.
--   $$
--
--   This gives the source's pure-state exponential stabilizer de finetti theorem in the fixed computational-basis and phase conventions.
--
--   **Formalization Note** Pure states carry norm one; stabilizer averages use density matrices to discard global phases. All finite tensor indices are explicitly ordered by copy, then physical qudit.
-- source:
--   Schur-Weyl Duality for the Clifford Group with Applications: Property Testing, a Robust Hudson Theorem, and de Finetti Representations, arXiv:1712.08628v3, PDF p. 54, theorem-7.2

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P30

noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Extend50.P30

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Gap20.P06 (ketBra)

attribute [local instance] Classical.propDecidable

/-- PDF p.54, Theorem 7.2: vector invariance and the full exponential bound; no small-error assumption. -/
theorem pureExponentialDeFinetti (d n t s : ℕ) [NeZero d] [Fact (Nat.Prime d)]
    (ht : 1 ≤ t) (hs : 1 ≤ s) (hst : s ≤ t)
    (v : EuclideanSpace ℂ (QuditCopies d n t)) (hv : ‖v‖ = 1) (hsym : IsPermutationSymmetric v)
    (hinv : ∀ O : StochasticOrthogonal d t,
      QAlgorithms.act (tensorRelation n (graphRelation O.val)) v = v) :
    ∃ p : QuditOperator d n → ℝ, IsDistributionOn (stabilizers d n) p ∧
      QAlgorithms.traceNorm (copyPrefixReduction s hst (QAlgorithms.pureDensity v) -
        stabilizerMixture s (stabilizers d n) p) / 2 ≤
          2 * Real.rpow (d : ℝ) (((n : ℝ) + 2) ^ 2 / 2) *
            Real.rpow (d : ℝ) (-((t - s : ℕ) : ℝ) / 2) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P30

end
