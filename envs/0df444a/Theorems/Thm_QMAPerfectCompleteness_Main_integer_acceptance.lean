-- Prove2me | Theorems.Thm_QMAPerfectCompleteness_Main_integer_acceptance
-- name    : QMAPerfectCompleteness.Main.integer_acceptance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:57:52.83428+00:00
-- url     : https://prove2.me/theorems/81d82e34-d8bf-46a1-8aa0-eebacde34b1f
-- title:
--   Corollary 3.2 — $2^{2g}E$ is an integer matrix
-- statement:
--   Let $V$ be a verifier over $\mathcal G_2$ with $g$ gates $H\otimes H$, counted literally in its gate list, and let $E$ be its acceptance operator as in Eq. (1). Then
--
--   $$
--   2^{2g}E\in\mathbb Z^{2^m\times 2^m}.
--   $$
--
--   The case $g=0$ is included. This gives the acceptance operator a known dyadic denominator of polynomial size.
--
--   Differences from the source: none.
-- source:
--   Sabee Grewal, Dorian Rudolph, QMA has perfect completeness, STOC 2027 submission #490 (October 2026), p. 7, Corollary 3.2

import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic

open Matrix

namespace QMAPerfectCompleteness.Main

/-- Corollary 3.2 (p. 7): for a verifier over `𝒢₂` with `g` gates `H ⊗ H`, the matrix `2^{2g} E`
has integer entries. -/
theorem integer_acceptance (V : Verifier gatesG2) :
    ∃ Z : Matrix V.Proof V.Proof ℤ,
      ((2 : ℂ) ^ (2 * hhCount V)) • V.acceptanceOperator = Z.map (Int.cast : ℤ → ℂ) := by sorry

end QMAPerfectCompleteness.Main
