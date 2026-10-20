-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P41_smoothConditionalAEP
-- name    : QAlgorithms.Papers.Independent.Dependency50.P41.smoothConditionalAEP
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:57:59.858154+00:00
-- url     : https://prove2.me/theorems/6a1ba9d5-7bd9-4d4e-9cb9-1ca8f0ad9c23
-- title:
--   Quantum-classical trace-norm smooth entropy AEP
-- statement:
--   All systems are finite-dimensional complex Hilbert spaces of positive dimension. Logarithms and entropies are in bits. Let $\rho_{AB}=\sum_k\rho_A^k\otimes|k\rangle\langle k|$ be normalized with positive A-blocks and orthonormal labels, let $n\ge1$, and let $\varepsilon>0$. Use extended conditional log-rank entropy and infimum smoothing over positive quantum-classical operators at full trace-norm distance at most $\varepsilon$, without a trace bound. On the implicit real formula domain $0<\varepsilon\le1$, $$\frac1nH_0^\varepsilon(A^n|B^n)_{\rho^{\otimes n}}\le H(A|B)_\rho+\frac{\log_2(|A|+3)\sqrt{\log_2(1/\varepsilon^2)}}{\sqrt n},$$ where $H(A|B)=H(AB)-H(B)$ and $|A|$ is the A-dimension. For $\varepsilon\ge1$, the smooth entropy itself equals $-\infty$.
--
--   This records the AEP and separately handles the zero-admissible tail, without totalizing a nonreal square root.
-- source:
--   Entanglement Cost of Quantum Channels, arXiv:1108.5357v3, PDF p. 21, Lemma 31

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P41

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P41

open scoped ComplexConjugate Matrix ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P06 (supportProjection)

open QAlgorithms.Papers.Independent.Information100.P08 (PureEnsemble formation pureAverage)

open QAlgorithms.Papers.Independent.Information100.P21 (Op FiniteLOCC spinFlip concurrence)

open QAlgorithms.Papers.Independent.Information100.P67 (conditionalEntropy groupedPower)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:1108.5357v3, PDF p.21, Lemma 31, (A12).
The real square-root formula is stated on its implicit domain epsilon<=1.
For epsilon>=1 the zero candidate gives minus infinity, recorded in the second clause.
Both clauses use the corrected INF in Definition 4 and FULL trace-norm smoothing. -/
theorem smoothConditionalAEP {A B : Type} {K : Type*} [Fintype A] [Fintype B] [Fintype K]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (v : K → EuclideanSpace ℂ B) (hv : Orthonormal ℂ v)
    (blocks : K → Op A) (hblocks : ∀ k, (blocks k).PosSemidef)
    (hstate : IsDensityMatrix (cqOperator v blocks))
    (n : ℕ) (hn : 1 ≤ n) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    (epsilon ≤ 1 →
      (((n : ℝ)⁻¹ : ℝ) : EReal) *
        smoothH0 (groupedPower (cqOperator v blocks) n) (labelPower v n) epsilon ≤
      ((conditionalEntropy (cqOperator v blocks) +
        Real.logb 2 (Fintype.card A + 3 : ℝ) * Real.sqrt (Real.logb 2 (1 / epsilon ^ 2)) /
          Real.sqrt (n : ℝ) : ℝ) : EReal)) ∧
    (1 ≤ epsilon →
      smoothH0 (groupedPower (cqOperator v blocks) n) (labelPower v n) epsilon = ⊥) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P41

end
