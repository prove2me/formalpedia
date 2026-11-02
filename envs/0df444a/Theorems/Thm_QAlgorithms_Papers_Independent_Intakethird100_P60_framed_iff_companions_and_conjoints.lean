-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P60_framed_iff_companions_and_conjoints
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P60.framed_iff_companions_and_conjoints
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:28:54.690678+00:00
-- url     : https://prove2.me/theorems/1e21379b-07bc-4358-a642-cf17e7ab1b7d
-- title:
--   Framing is exactly existence of companions and conjoints
-- statement:
--   Let $\mathbb D$ be a pseudo double category. A companion and a conjoint mean the typed cells and both vertical and horizontal identities of Definition A.1, with the horizontal identities interpreted using the specified unitors. Then
--
--   $$
--   \mathbb D\text{ is a framed bicategory}
--   \quad\Longleftrightarrow\quad
--   \forall(f:A\to B),\ f\text{ has both a companion and a conjoint}.
--   $$
--
--   Framing means that the joint frame functor $(L,R)$ is a fibration; its cartesian cells have the full factorization property over arbitrary further base arrows. All object and morphism universes are fixed independently, so categories may be large.
--
--   This is the companion/conjoint form of the framing criterion.
-- source:
--   Framed bicategories and monoidal fibrations, arXiv:0706.1286v2, PDF p. 72, Theorem A.2: Framing iff companions and conjoints

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P60

namespace QAlgorithms.Papers.Independent.Intakethird100.P60

open CategoryTheory

universe u v w x

/-- Theorem A.2 (PDF p. 72): both kinds of lift are required. -/
theorem framed_iff_companions_and_conjoints {V : Type u} [Category.{v} V]
    (D : DoubleData.{u,v,w,x} V) (hD : DoubleCoherence D) :
    IsFramed D ↔ HasCompanions D ∧ HasConjoints D := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P60
