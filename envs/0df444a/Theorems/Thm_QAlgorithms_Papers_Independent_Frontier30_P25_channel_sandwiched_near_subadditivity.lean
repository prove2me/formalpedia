-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P25_channel_sandwiched_near_subadditivity
-- name    : QAlgorithms.Papers.Independent.Frontier30.P25.channel_sandwiched_near_subadditivity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:42:30.263716+00:00
-- url     : https://prove2.me/theorems/5129b385-28d5-48be-8148-76d6933e6101
-- title:
--   Near-subadditivity of channel sandwiched REE
-- statement:
--   Let $\mathcal N:A\to B$ be a CPTP map between nonzero finite-dimensional systems, let $d=\dim A$, let $\alpha>1$, and let $n\ge1$ be an integer. Define $\widetilde E_{R,\alpha}(\mathcal N)$ as the supremum, over normalized pure inputs on a reference isomorphic to $A$ and the channel input, of the sandwiched Rényi relative entropy of entanglement of the actual channel output. The entanglement quantity takes its infimum over all separable comparison states across reference and output, in bits. Then
--
--   $$\widetilde E_{R,\alpha}(\mathcal N^{\otimes n})\le n\widetilde E_{R,\alpha}(\mathcal N)+\frac{\alpha}{\alpha-1}d^2\log_2 n.$$
--
--   The correction uses squared Hilbert-space dimension. It vanishes at $n=1$. This estimate controls the polynomial prefactor in the CPPP strong-converse exponent.
-- source:
--   Converse bounds for private communication over quantum channels, arXiv:1602.08898v3, PDF p. 23, Theorem 15

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P25

noncomputable section

namespace QAlgorithms.Papers.Independent.Frontier30.P25

open scoped Matrix ComplexConjugate ENNReal

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Pinned accepted definitions; assessments record the domains of equivalence.

open QAlgorithms.Papers.Independent.Dependency50.P09 (OneDesign relativeD sandwichedD)

open QAlgorithms.Papers.Independent.Dependency50.P24 (logBits idealCCQ)

open QAlgorithms.Papers.Independent.Information100.P22 (bell)

open QAlgorithms.Papers.Independent.Information100.P58 (testingD)

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity privateState privacyTest)

/-- PDF p.23, Theorem 15: correction uses squared input dimension, not qubit count.
Positive n guards log n; at n=1 the correction vanishes. -/
theorem channel_sandwiched_near_subadditivity
    {A B : Type} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    (N : Superop A B) (hN : IsChannel N) (alpha : ℝ) (halpha : 1 < alpha)
    (n : ℕ) (hn : 1 ≤ n) :
    channelSandwiched alpha (piSuperop (fun _ : Fin n => N)) ≤
      (n : EReal) * channelSandwiched alpha N +
      ((alpha / (alpha - 1) * (Fintype.card A : ℝ)^2 * logBits n : ℝ) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P25

end
