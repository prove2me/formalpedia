-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P24_entropyHierarchy
-- name    : QAlgorithms.Papers.Independent.Renew46.P24.entropyHierarchy
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T20:43:32.59035+00:00
-- url     : https://prove2.me/theorems/d2b25544-ebd0-4a4b-95d5-3062319b6766
-- title:
--   §3 opening: order of the three ensemble entropies
-- statement:
--   For an arbitrary uniformly operator-norm bounded self-adjoint family $X_k^N$ on nonzero finite-dimensional complex Hilbert spaces and a real configuration $x$, let $H^{\rm mc}(x)$ be the supremum of projection log-dimension densities over concentrating nonzero projection sequences. Let $H^{\rm can}(x)$ be the entropy-density supremum over normalized states concentrating under all joint analytic tests, and let $H_1^{\rm can}(x)$ be the analogous supremum requiring only convergence of the means to $x$. Every supremum is taken over sequences before taking the volume limsup, and takes values in the extended real line. Then
--
--   $$H^{\rm mc}(x)\le H^{\rm can}(x)\le H_1^{\rm can}(x).$$
--
--   Empty feasible classes have value $-\infty$. This comparison provides the general order of the three ensemble entropies without assuming attainment.
-- source:
--   Quantum Macrostates, Equivalence of Ensembles and an H-Theorem, arXiv:math-ph/0601027v2, PDF p. 8, §3 opening: order of the three ensemble entropies

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P24

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P24

open Filter

open scoped Topology ComplexOrder Matrix.Norms.L2Operator

-- Exact primitives verified against the pinned accepted-library SHA256 catalogue.

open QAlgorithms.Papers.Independent.Information100.P23 (Operator)

open QAlgorithms.Papers.Independent.Dependency50.P21 (spectralFunction relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P10 (pauli)

open QAlgorithms.Papers.Independent.Information100.P71 (SupportIncluded)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.8, opening comparison: the three extended-real ensemble entropies
are ordered at every real configuration, including empty feasible classes. -/
theorem entropyHierarchy {K : Type*} (S : MacroscopicSystem K)
    (hS : IsMacroscopic S) (x : K → ℝ) :
    microcanonicalEntropy S x ≤ canonicalEntropy S x ∧
      canonicalEntropy S x ≤ meanCanonicalEntropy S x := by sorry

end QAlgorithms.Papers.Independent.Renew46.P24

end
