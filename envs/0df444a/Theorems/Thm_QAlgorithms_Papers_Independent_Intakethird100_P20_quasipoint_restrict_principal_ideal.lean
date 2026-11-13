-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_quasipoint_restrict_principal_ideal
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.quasipoint_restrict_principal_ideal
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-12T17:08:02.382134+00:00
-- url     : https://prove2.me/theorems/2ff5fa6b-f999-4876-b3f0-dae7679024fd
-- title:
--   A quasipoint containing a restricts to a quasipoint of the principal ideal
-- statement:
--   Let $L$ be a bounded lattice, let $a\in L$, and let $B$ be a quasipoint with $a\in B$. For the principal ideal $L_a=\{b:b\le a\}$, with its inherited order and least element $0$, the restriction
--
--   $$B|_{L_a}=\{b\in L_a:b\in B\}$$
--
--   is a quasipoint of the principal ideal. This is the well-definedness step for restricting the Stone spectrum to the basic open Q_a.
-- source:
--   H. F. de Groote, Observables I: Stone Spectra, arXiv:math-ph/0509020v1, https://arxiv.org/pdf/math-ph/0509020v1, proof of Proposition 3.21, printed p.65 (PDF p.66): the principal-ideal Stone spectrum is homeomorphic to Q_a. This supporting lemma isolates the restriction map.

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

namespace QAlgorithms.Papers.Independent.Intakethird100.P20
theorem quasipoint_restrict_principal_ideal {L : Type*} [Lattice L] [BoundedOrder L]
    (a : L) (B : StoneSpectrum L) (hBa : a ∈ B.val) :
    letI : Bot (Set.Iic a) := ⟨⟨⊥, bot_le⟩⟩
    IsQuasipoint {b : Set.Iic a | b.val ∈ B.val} := by sorry
end QAlgorithms.Papers.Independent.Intakethird100.P20
