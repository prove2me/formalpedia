-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P23_finiteUseConverses
-- name    : QAlgorithms.Papers.Independent.Dependency50.P23.finiteUseConverses
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:34:29.023997+00:00
-- url     : https://prove2.me/theorems/44b5e9f7-82a5-4334-9527-01971d1197a2
-- title:
--   Corollary 5: finite-use converses for EA and unassisted codes
-- statement:
--   Let $\mathcal N:A\to B$ be a CPTP channel on nonzero finite registers, and $0\le e<1$. Write $C_E^{(1)}$ for the operational integer-message entanglement-assisted capacity, with arbitrary finite shared states and local CPTP encoding and decoding, and $C^{(1)}$ for its unassisted counterpart. The NS quantities below use the continuous SDP convention. Then
--
--   $$C_E^{(1)}(\mathcal N,e)\le C_{\mathrm{NS}}^{(1)}(\mathcal N,e),\qquad C^{(1)}(\mathcal N,e)\le C_{\mathrm{NS}\cap\mathrm{PPT}}^{(1)}(\mathcal N,e).$$
--
--   These are finite-use converse bounds for average error under uniform messages, with no communication resource other than the channel.
-- source:
--   Semidefinite programming strong converse bounds for classical capacity, arXiv:1610.06381v4, PDF p. 10, Corollary 5

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P23

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P23

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

open QAlgorithms.Papers.Independent.Information100.P80 (log2 quantumCapacity)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

variable {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

/-- PDF p.10, Corollary 5: finite-use converses for EA and ordinary local codes. -/
theorem finiteUseConverses [Nonempty A] [Nonempty B] (N : Superop A B) (hN : IsChannel N)
    (e : ℝ) (he0 : 0 ≤ e) (he1 : e < 1) :
    integerOneShot (eaSuccess N) e ≤ oneShot false N e ∧
    integerOneShot (uaSuccess N) e ≤ oneShot true N e := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P23

end
