-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_order_iso_maps_quasipoints
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.order_iso_maps_quasipoints
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-12T16:27:47.660196+00:00
-- url     : https://prove2.me/theorems/e00dd4d2-d1b0-4b94-8022-92b62cd9dede
-- title:
--   Order isomorphisms carry quasipoints to quasipoints
-- statement:
--   Let $L$ and $K$ be bounded lattices, and let $e:L\to K$ be an order isomorphism. For every quasipoint $B$ of $L$, the image
--
--   $$e[B]=\{e(a):a\in B\}$$
--
--   is a quasipoint of K, meaning a maximal proper nonempty filter base. This proves that the induced map on Stone spectra is well defined, the algebraic step in the lattice-isomorphism homeomorphism construction. Completeness is unnecessary for this step.
-- source:
--   H. F. de Groote, Observables I: Stone Spectra, arXiv:math-ph/0509020v1, https://arxiv.org/pdf/math-ph/0509020v1, Section 3.3, printed p.54 (PDF p.55), displayed definition of the induced map Φ* immediately before Lemma 3.4.

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20
open Set

namespace QAlgorithms.Papers.Independent.Intakethird100.P20
theorem order_iso_maps_quasipoints {L : Type*} {K : Type*} [Lattice L] [BoundedOrder L]
    [Lattice K] [BoundedOrder K] (e : L ≃o K) (B : Set L) (hB : IsQuasipoint B) :
    IsQuasipoint (e '' B) := by sorry
end QAlgorithms.Papers.Independent.Intakethird100.P20
