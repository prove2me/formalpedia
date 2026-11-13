-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_quasipoint_extend_principal_ideal
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.quasipoint_extend_principal_ideal
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-12T17:13:06.652242+00:00
-- url     : https://prove2.me/theorems/770eb1f6-dd14-4d3a-be68-3a2a9b7f7392
-- title:
--   A principal-ideal quasipoint extends upward to a quasipoint
-- statement:
--   Let $L$ be a partially ordered set with least element $0$, let $a\in L$, and let $C$ be a quasipoint of the principal ideal $L_a=\{c:c\le a\}$. Then
--
--   $$\uparrow C=\{b\in L:\exists c\in C,\ c\le b\}$$
--
--   is a quasipoint of L. This is the extension map inverse to principal-ideal restriction in the Stone-spectrum correspondence. The construction itself requires neither joins nor meets.
-- source:
--   H. F. de Groote, Observables I: Stone Spectra, arXiv:math-ph/0509020v1, https://arxiv.org/pdf/math-ph/0509020v1, proof of Proposition 3.21, printed p.65 (PDF p.66), principal-ideal spectrum correspondence. This supporting lemma isolates the upward extension and records its weaker order-theoretic assumptions.

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

namespace QAlgorithms.Papers.Independent.Intakethird100.P20
theorem quasipoint_extend_principal_ideal {L : Type*} [PartialOrder L] [OrderBot L]
    (a : L) :
    letI : Bot (Set.Iic a) := ⟨⟨⊥, bot_le⟩⟩
    ∀ C : StoneSpectrum (Set.Iic a), IsQuasipoint {b : L | ∃ c ∈ C.val, c.val ≤ b} := by sorry
end QAlgorithms.Papers.Independent.Intakethird100.P20
