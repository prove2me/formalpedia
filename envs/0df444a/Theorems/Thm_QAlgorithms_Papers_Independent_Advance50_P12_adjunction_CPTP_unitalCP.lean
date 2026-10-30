-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P12_adjunction_CPTP_unitalCP
-- name    : QAlgorithms.Papers.Independent.Advance50.P12.adjunction_CPTP_unitalCP
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:14:41.556969+00:00
-- url     : https://prove2.me/theorems/1e0bc5a2-9caa-45c1-9a4e-315787992d1f
-- title:
--   Lemma 2: adjunction exchanges CPTP and unital CP maps
-- statement:
--   Let $H_A,H_B$ be positive-dimensional finite-dimensional complex Hilbert spaces. For a complex-linear map $\Phi:L(H_A)\to L(H_B)$, define its trace-pairing adjoint by
--   $$\operatorname{tr}(Y\Phi(X))=\operatorname{tr}(\Phi^\dagger(Y)X)\quad\text{for every }X,Y.$$
--   Adjunction is a bijection
--   $$\dagger:\mathrm{CPTPM}(H_A,H_B)\longrightarrow\mathrm{CPUM}(H_B,H_A),$$
--   with inverse the same adjunction in the reverse direction. Here CPTPM means completely positive and trace-preserving on all operators; CPUM means completely positive and unital. Complete positivity includes every finite ancillary extension. Explicitly, each direction lands in the stated class and $(\Phi^\dagger)^\dagger=\Phi$ in both classes. This converts quantum operations into unital maps without a state hypothesis.
-- source:
--   The operational meaning of min- and max-entropy, arXiv:0807.1338v2, PDF p. 7, Lemma 2

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P12

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P12

open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P07 (CQData cqDensity)

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative elog marginalAB)

open QAlgorithms.Papers.Independent.Information100.P67 (conditionalMinEntropy)

open QAlgorithms.Papers.Independent.Renew46.P35 (traceAdjoint)

open QAlgorithms.Papers.Independent.Support50.P23 (exp2Extended independentProduct)

variable {A B C D X : Type}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype X]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D] [DecidableEq X]

/-- PDF p.7, Lemma 2: trace adjunction maps CPTP to unital CP and conversely,
and the same adjunction is an inverse in both directions. -/
theorem adjunction_CPTP_unitalCP [Nonempty A] [Nonempty B] :
    (∀ f : Superop A B, IsChannel f →
      UnitalCP (traceAdjoint f) ∧ traceAdjoint (traceAdjoint f) = f) ∧
    (∀ g : Superop B A, UnitalCP g →
      IsChannel (traceAdjoint g) ∧ traceAdjoint (traceAdjoint g) = g) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P12

end
