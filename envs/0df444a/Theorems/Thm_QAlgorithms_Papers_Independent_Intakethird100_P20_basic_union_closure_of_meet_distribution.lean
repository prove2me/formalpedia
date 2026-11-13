-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_basic_union_closure_of_meet_distribution
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.basic_union_closure_of_meet_distribution
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-12T16:17:05.125851+00:00
-- url     : https://prove2.me/theorems/bcb6b60d-ac30-43ca-9bc0-4d7ac38596a0
-- title:
--   Meet distribution over a family determines its basic-union closure
-- statement:
--   Let $L$ be a complete lattice and $S\subseteq L$. Suppose every $b\in L$ satisfies
--
--   $$b\wedge\bigvee S=\bigvee_{a\in S}(b\wedge a).$$
--
--   Then, in the Stone spectrum of maximal proper filter bases,
--
--   $$\overline{\bigcup_{a\in S}Q_a}=Q_{\bigvee S}.$$
--
--   Only distribution over the specified family is required. This is the common implication used for complete frames and for directed families in lattices of finite type.
-- source:
--   H. F. de Groote, Observables I: Stone Spectra, arXiv:math-ph/0509020v1, https://arxiv.org/pdf/math-ph/0509020v1, Proposition 3.7 and proof, printed p.44; Lemma 3.2, printed p.45, converse by the same argument. The hypothesis is restricted to the family used in the proof.

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20
open Set TopologicalSpace

namespace QAlgorithms.Papers.Independent.Intakethird100.P20
theorem basic_union_closure_of_meet_distribution {L : Type*} [CompleteLattice L]
    (s : Set L) (hdistrib : ∀ b : L, b ⊓ sSup s = sSup ((fun a => b ⊓ a) '' s)) :
    closure (⋃ a ∈ s, stoneBasic a) = stoneBasic (sSup s) := by sorry
end QAlgorithms.Papers.Independent.Intakethird100.P20
