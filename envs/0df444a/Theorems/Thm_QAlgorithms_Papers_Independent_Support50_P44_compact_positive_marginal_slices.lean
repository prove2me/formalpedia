-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P44_compact_positive_marginal_slices
-- name    : QAlgorithms.Papers.Independent.Support50.P44.compact_positive_marginal_slices
-- status  : Open
-- author  : @Goku
-- created : 2026-10-24T00:03:53.47767+00:00
-- url     : https://prove2.me/theorems/60478d4e-7511-420d-8fa8-1a871ceac008
-- title:
--   Compact positive marginal slices
-- statement:
--   Let $E,G$ be finite-dimensional complex Hilbert spaces and let $\sigma_G\ge0$ be an operator on $G$. Both sets
--
--   $$\{X\ge0\text{ on }E\otimes G:\operatorname{tr}_E X\le\sigma_G\},\qquad \{X\ge0\text{ on }E\otimes G:\operatorname{tr}_E X=\sigma_G\}$$
--
--   are compact. The inequality is the positive-semidefinite order. The reference operator need not be normalized or invertible; these slices control fixed-marginal extension sets.
-- source:
--   Universal recovery map for approximate Markov chains, arXiv:1504.07251v3, PDF p. 25, Lemma C.2

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P44

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsTraceClass compression)

open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

open QAlgorithms.Papers.Independent.Renew46.P37 (classicalKL)

open Filter

open scoped ENNReal ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {A B C E G : Type*}

/-- PDF pp.25–26, Lemma C.2: both marginal slices; sigma need only be positive.
The proof's rhoG is read as the fixed sigmaG from its statement. -/
theorem compact_positive_marginal_slices [Fintype E] [Fintype G]
    [DecidableEq E] [DecidableEq G]
    (sigma : Matrix G G ℂ) (hsigma : sigma.PosSemidef) :
    IsCompact {X : Matrix (E × G) (E × G) ℂ |
      X.PosSemidef ∧ (sigma - traceLeft X).PosSemidef} ∧
    IsCompact {X : Matrix (E × G) (E × G) ℂ |
      X.PosSemidef ∧ traceLeft X = sigma} := by sorry

end QAlgorithms.Papers.Independent.Support50.P44

end
