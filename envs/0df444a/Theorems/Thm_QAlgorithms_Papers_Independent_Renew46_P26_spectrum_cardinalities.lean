-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P26_spectrum_cardinalities
-- name    : QAlgorithms.Papers.Independent.Renew46.P26.spectrum_cardinalities
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:51:01.763274+00:00
-- url     : https://prove2.me/theorems/f89c911e-16c5-49a0-96bd-0e0e1ca5e0f4
-- title:
--   Unnumbered spectrum and dimension identities
-- statement:
--   Let $\widehat S_n$ be the actual equivalence classes of nonzero finite-dimensional irreducible complex representations. Define $\operatorname{Spec}(n)$ from nonzero joint eigenvectors of the actual $X_1,\ldots,X_n$, and let $\sim$ mean occurrence in the same irreducible. Then $\widehat S_n$ is finite and
--
--   $$|\operatorname{Spec}(n)|=\dim_{\mathbb C}GZ(n)=\sum_{\lambda\in\widehat S_n}\dim V^\lambda,\qquad |\operatorname{Spec}(n)/\sim|=|\widehat S_n|.$$
--
--   There is a bijection between actual branching paths and spectral weights, respecting each prefix's irreducible vertex. These identities describe the global spectrum across all irreducibles.
-- source:
--   A New Approach to the Representation Thoery of the Symmetric Groups. 2, arXiv:math/0503040v3, PDF p. 13, Unnumbered spectrum and dimension identities

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P26

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P26

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Spectrum and dimension identities (PDF p.13), including the natural
path correspondence and the quotient count. A finite enumeration of actual
irreducible classes is part of the conclusion; no sum uses an infinite-type
fallback. Quot generates the stated same-irreducible equivalence relation. -/
theorem spectrum_cardinalities (n : ℕ) :
    ∃ F : Fintype (IrreducibleClass n),
      letI := F
      Nat.card {alpha : Fin n → ℂ // alpha ∈ spectrum n} =
        ∑ C : IrreducibleClass n, (classRepresentative C).dimension ∧
      Module.finrank ℂ (gzAlgebra n) =
        ∑ C : IrreducibleClass n, (classRepresentative C).dimension ∧
      (∃ e : BranchingPath n ≃ {alpha : Fin n → ℂ // alpha ∈ spectrum n},
        ∀ T, PathHasWeight T (e T).val) ∧
      Nat.card (Quot (fun a b : {alpha : Fin n → ℂ // alpha ∈ spectrum n} =>
        SameIrreducible a.val b.val)) = Fintype.card (IrreducibleClass n) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P26

end
