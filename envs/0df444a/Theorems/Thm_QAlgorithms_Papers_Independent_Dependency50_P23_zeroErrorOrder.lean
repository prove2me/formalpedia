-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P23_zeroErrorOrder
-- name    : QAlgorithms.Papers.Independent.Dependency50.P23.zeroErrorOrder
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:50:18.523779+00:00
-- url     : https://prove2.me/theorems/b3072634-de14-42e6-9f68-2a16eede68e1
-- title:
--   Unnumbered consequence: one-shot zero-error converse hierarchy
-- statement:
--   Let $\mathcal N:A\to B$ be a CPTP channel on nonzero finite registers. Let $M_0(\mathcal N)$ be the maximum integer number of unassisted messages whose outputs are perfectly distinguishable by a POVM, and let the assisted quantities denote their continuous zero-error SDP relaxations. Then
--
--   $$M_0(\mathcal N)\le M_{0,\mathrm{NS}\cap\mathrm{PPT}}(\mathcal N)\le M_{0,\mathrm{NS}}(\mathcal N).$$
--
--   These are message numbers, without logarithms. The hierarchy gives computable converses for unassisted one-shot zero-error transmission.
-- source:
--   Semidefinite programming strong converse bounds for classical capacity, arXiv:1610.06381v4, PDF p. 21, Unnumbered consequence

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

/-- PDF p.21, unnumbered consequence: integer UA message optimum versus the
continuous NS∩PPT and NS message relaxations. -/
theorem zeroErrorOrder [Nonempty A] [Nonempty B] (N : Superop A B) (hN : IsChannel N) :
    uaZeroMessages N ≤ zeroMessages true N ∧
    zeroMessages true N ≤ zeroMessages false N := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P23

end
