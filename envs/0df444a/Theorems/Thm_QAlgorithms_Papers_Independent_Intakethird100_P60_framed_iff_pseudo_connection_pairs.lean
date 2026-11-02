-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P60_framed_iff_pseudo_connection_pairs
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P60.framed_iff_pseudo_connection_pairs
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:29:20.326527+00:00
-- url     : https://prove2.me/theorems/9ea130d1-2713-43a5-803f-e90f6218febf
-- title:
--   Framing is exactly existence of both pseudo connection pairs
-- statement:
--   Let $\mathbb D$ be a pseudo double category. A pseudo connection pair is a choice, for every vertical arrow, of a companion with its two cells and its two identities. A pseudo op-connection pair is the corresponding choice of conjoints. Then
--
--   $$
--   \mathbb D\text{ is framed}
--   \quad\Longleftrightarrow\quad
--   \mathbb D\text{ admits a pseudo connection pair and a pseudo op-connection pair}.
--   $$
--
--   The horizontal composition need not be strict, and no split cleavage or strict connection axiom is imposed. Both choices are part of the conclusion.
--
--   This packages the nonalgebraic existence characterization as chosen pseudo connection data.
-- source:
--   Framed bicategories and monoidal fibrations, arXiv:0706.1286v2, PDF p. 72, AppendixA: pseudo connection-pair characterization

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P60

namespace QAlgorithms.Papers.Independent.Intakethird100.P60

open CategoryTheory

universe u v w x

/-- Appendix A pseudo connection-pair characterization (PDF p. 72).
These are arbitrary choices in a pseudo double category, not strict connections. -/
theorem framed_iff_pseudo_connection_pairs {V : Type u} [Category.{v} V]
    (D : DoubleData.{u,v,w,x} V) (hD : DoubleCoherence D) :
    IsFramed D ↔ Nonempty (PseudoConnectionPair D) ∧ Nonempty (PseudoOpConnectionPair D) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P60
