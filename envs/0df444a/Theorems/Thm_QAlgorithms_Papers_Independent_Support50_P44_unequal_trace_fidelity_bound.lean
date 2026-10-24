-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P44_unequal_trace_fidelity_bound
-- name    : QAlgorithms.Papers.Independent.Support50.P44.unequal_trace_fidelity_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T23:58:47.114975+00:00
-- url     : https://prove2.me/theorems/fe06a381-8fc2-47fa-a40b-af6cfd4fe34c
-- title:
--   Trace distance bound for positive operators of unequal trace
-- statement:
--   Let $\rho$ and $\sigma$ be positive trace-class operators on a complex separable Hilbert space, with $\operatorname{tr}\rho\ge\operatorname{tr}\sigma$. With $\|\cdot\|_1$ the trace norm and $F$ root fidelity,
--
--   $$\|\rho-\sigma\|_1\le 2\sqrt{(\operatorname{tr}\rho)^2-F(\rho,\sigma)^2}.$$
--
--   No normalization or upper bound on either trace is imposed. The inequality also covers the zero operators and is used for subnormalized recovered states.
-- source:
--   Universal recovery map for approximate Markov chains, arXiv:1504.07251v3, PDF p. 24, Lemma A.2

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

/-- PDF pp.23–24, Lemma A.2, (143): arbitrary positive trace-class operators.
Neither normalization nor trace at most one is imposed. The proof's incorrect (144)
is not part of this statement. -/
theorem unequal_trace_fidelity_bound {I : Type*} [Countable I] (b : HilbertBasis I ℂ H)
    (rho sigma : H →L[ℂ] H) (hrho : IsTraceClass rho) (hsigma : IsTraceClass sigma)
    (hposrho : rho.IsPositive) (hpossigma : sigma.IsPositive)
    (htrace : (hilbertTrace b sigma).re ≤ (hilbertTrace b rho).re) :
    hilbertTraceNorm b (rho - sigma) ≤
      2 * Real.sqrt ((hilbertTrace b rho).re ^ 2 - hilbertFidelity b rho sigma ^ 2) := by sorry

end QAlgorithms.Papers.Independent.Support50.P44

end
