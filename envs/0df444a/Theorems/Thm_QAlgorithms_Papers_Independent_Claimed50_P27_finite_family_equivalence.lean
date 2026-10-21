-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P27_finite_family_equivalence
-- name    : QAlgorithms.Papers.Independent.Claimed50.P27.finite_family_equivalence
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:17:01.519132+00:00
-- url     : https://prove2.me/theorems/8450c20f-0474-4934-82dc-5e11ed8b2afe
-- title:
--   Finite-family exact cloning and perfect discrimination
-- statement:
--   Let $k\ge1$ and let $\Phi_1,\ldots,\Phi_k$ be known CPTP devices with the same finite, nonempty input and output registers. Let $p_{ij}$ be the optimal worst conditional error for physically discriminating $\Phi_i$ and $\Phi_j$ with one use, using normalized probes, references and POVMs. Assume $p_{ij}\ne1/2$ whenever $i\ne j$. Then
--
--   $$\text{one common deterministic one-use exact cloner exists}\ \Longleftrightarrow\ \text{one-use perfect family discrimination is possible}.$$
--
--   Exact cloning means equality to $\Phi_i\otimes\Phi_i$ for every candidate and every joint input. Perfect discrimination means one common physical $k$-outcome test identifies every candidate with probability one. In particular the equivalence holds for a duplicate-free finite set of CPTP channels, since distinct finite channels are operationally distinguishable. Singleton sets are included.
--
--   The result relates perfect device replication to physical identification. Duplicate labels must be quotiented before using the duplicate-free formulation; the conditional formulation itself excludes indistinguishable distinct labels.
-- source:
--   Optimal cloning of unitary transformations, arXiv:0804.0129v2, PDF p. 1, Unnumbered equivalence; footnote [18], p.4

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P27

noncomputable section

open MeasureTheory QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

namespace QAlgorithms.Papers.Independent.Claimed50.P27

attribute [local instance] Classical.decEq Classical.propDecidable

/-- PDF p.1 and footnote [18], p.4: the pairwise condition is only for distinct
indices. The second clause states the resulting duplicate-free finite-channel
specialization. Singleton families are allowed; empty families are excluded. -/
theorem finite_family_equivalence {I O : Type*} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] [Nonempty I] [Nonempty O]
    (k : ℕ) (hk : 1 ≤ k) (family : Fin k → Superop I O)
    (hfamily : ∀ i, IsChannel (family i)) :
    ((∀ i j : Fin k, i ≠ j → minimaxError (family i) (family j) ≠ 1 / 2) →
      (ExactlyClonable family ↔ PerfectlyDiscriminable family)) ∧
    (Function.Injective family →
      (ExactlyClonable family ↔ PerfectlyDiscriminable family)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P27

end
