-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_filter_base_upward_closure
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.filter_base_upward_closure
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-12T17:03:34.945193+00:00
-- url     : https://prove2.me/theorems/75567618-2ebe-4760-a8b1-addb117d1823
-- title:
--   The upward closure of a proper filter base is a proper filter base
-- statement:
--   Let $L$ be a partially ordered set with least element $0$, and let $B\subseteq L$ be a proper nonempty directed filter base. Its upward closure
--
--   $$\uparrow B=\{x\in L:\exists b\in B,\ b\le x\}$$
--
--   is again a proper nonempty directed filter base. This basic extension operation supports the restriction and extension of quasipoints along principal ideals, and does not require lattice operations.
-- source:
--   Supporting filter-base lemma for H. F. de Groote, Observables I: Stone Spectra, arXiv:math-ph/0509020v1, https://arxiv.org/pdf/math-ph/0509020v1, Definition 3.3 and Proposition 3.4, printed pp.37–38; principal-ideal spectrum correspondence used in the proof of Proposition 3.21, printed p.65 (PDF p.66). The upward-closure operation is formalized separately here.

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

namespace QAlgorithms.Papers.Independent.Intakethird100.P20
theorem filter_base_upward_closure {L : Type*} [PartialOrder L] [OrderBot L]
    (B : Set L) (hB : IsFilterBase B) :
    IsFilterBase {x : L | ∃ b ∈ B, b ≤ x} := by sorry
end QAlgorithms.Papers.Independent.Intakethird100.P20
