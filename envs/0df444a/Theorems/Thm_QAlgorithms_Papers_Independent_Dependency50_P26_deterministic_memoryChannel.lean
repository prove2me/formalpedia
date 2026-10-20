-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P26_deterministic_memoryChannel
-- name    : QAlgorithms.Papers.Independent.Dependency50.P26.deterministic_memoryChannel
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:38:01.557104+00:00
-- url     : https://prove2.me/theorems/0bec601e-323b-4c65-8d77-aac0aea27f55
-- title:
--   Corollary 3: combs are memory channels
-- statement:
--   All Hilbert spaces are finite-dimensional complex spaces of positive dimension with fixed orthonormal bases. Every operationally deterministic $N$-comb $R$, for $N\ge1$, is the Choi operator of an $N$-partite memory channel. The realization furnished by the source can be chosen isometric with final memory trace:
--
--   $$
--   \exists\text{ sequential isometric memory network }\mathcal V,\qquad C(\mathcal V)=R.
--   $$
--
--   This identifies the axiomatic deterministic objects with the constructive networks.
-- source:
--   Theoretical framework for quantum networks, arXiv:0904.4483v2, PDF p. 12, Corollary 3: combs are memory channels

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P26

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Dependency50.P26

/-- PDF p.12, Corollary 3: an N-partite memory channel, with the same Choi operator. -/
theorem deterministic_memoryChannel (s : Signature) (n : ℕ) (hn : 0 < n)
    (R : Matrix (Basis s n) (Basis s n) ℂ) (hR : Deterministic n s R) :
    ∃ net : IsometricNetwork s, net.choi n = R := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P26

end
