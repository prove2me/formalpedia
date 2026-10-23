-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P04_lemma12
-- name    : QAlgorithms.Papers.Independent.Gap20.P04.lemma12
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T06:52:06.164377+00:00
-- url     : https://prove2.me/theorems/e33e05ac-739d-467c-97df-7e0f234ecdfb
-- title:
--   Lemma-12
-- statement:
--   Let $\mathcal N$ be a generalized-dephasing channel with isometry $U|i\rangle=|i\rangle|v_i\rangle$, where each environment vector has norm one and the vectors need not be orthogonal. Let $e$ be any physical finite ensemble of pure reference-input states. Form another such ensemble $t$ with the same probabilities and conditional input marginals $\Delta(\rho_x^{A'})$, choosing fresh pure purifications on any finite reference. Both ensembles pass through the same $U$.
--
--   For every $\lambda\ge1$,
--   $$\chi(e)+\lambda q(e)\le\chi(t)+\lambda q(t),$$
--   where $\chi=I(X;B)$ and $q=I(A\rangle BX)$ in bits. Diagonal input marginals therefore suffice for the CQ optimization.
-- source:
--   Trade-off capacities of the quantum Hadamard channels, arXiv:1001.1732v2, PDF p. 21, Lemma-12

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P04

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P04

open QAlgorithms

open QAlgorithms.Papers.Independent.Claimed50.P24
  (Dilation PhysicalDilation ChannelEB Hadamard EqualMax AdditiveMax
   dephasingDilation dephasingGamma cloningDilation)

open QAlgorithms.Papers.Independent.Information100.P67
  (receiverChannel complementaryChannel dilationPower)

open QAlgorithms.Papers.Independent.Information100.P32 (diagonal)

open QAlgorithms.Papers.Independent.Dependency50.P24 (ensembleHolevoBits)

open QAlgorithms.Papers.Independent.Gap48.P44 (cqTimeSharing ceTimeSharing)

open scoped BigOperators Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I B E J D F : Type}

variable [Fintype I] [Fintype B] [Fintype E]

variable [Fintype J] [Fintype D] [Fintype F]

variable [DecidableEq I] [DecidableEq B] [DecidableEq E]

variable [DecidableEq J] [DecidableEq D] [DecidableEq F]

variable [Nonempty I] [Nonempty B] [Nonempty E]

variable [Nonempty J] [Nonempty D] [Nonempty F]

/-- PDF p.21, Lemma 12: dephase input marginals and REPURIFY, with unchanged weights.
Arbitrary purifying reference dimensions are permitted on each side. -/
theorem lemma12 (v : I → EuclideanSpace ℂ E) (hv : ∀ i, ‖v i‖ = 1)
    (e t : PurifiedInputFamily I) (he : e.Valid) (ht : t.Valid)
    (hreplace : DephasedReplacement e t) (lam : ℝ) (hlam : 1 ≤ lam) :
    cqScore (gdDilation v) lam e ≤ cqScore (gdDilation v) lam t := by sorry

end QAlgorithms.Papers.Independent.Gap20.P04

end
