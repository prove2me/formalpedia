-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P12_cyclotomic_recurrence
-- name    : QAlgorithms.Papers.Independent.Support21.P12.cyclotomic_recurrence
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:07:00.071683+00:00
-- url     : https://prove2.me/theorems/a0bbbcae-143c-481b-92c8-e184e411904e
-- title:
--   Scalar-faithful contraction forces the cyclotomic recurrence
-- statement:
--   Let $S$ be a commutative unital ring and let $A_2$ be either actual cyclotomic BMW algebra of positive degree $r$, with all ordinary unit and compatibility conditions when appropriate. Suppose that $s\mapsto se_1$ is injective. Define $a_j\in S$ by $p(T)=\prod_{i=1}^r(T-u_i)=\sum_{j=0}^r a_jT^j$. Then
--
--   $$\sum_{j=0}^r a_j\omega_{j+\ell}=0\qquad(\ell\ge0).$$
--
--   This is a recurrence for the parameter sequence itself, obtained under scalar faithfulness of the contraction.
-- source:
--   Remarks on Cyclotomic and Degenerate Cyclotomic BMW Algebras, arXiv:1011.3284v3, PDF p. 4, Lemma 2.7

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P12

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Support21.P12

/-- Lemma 2.7, PDF pp.4--5. 'Not torsion' means that s↦s e_1 is injective. -/
theorem cyclotomic_recurrence (S : Type*) [CommRing S] (omega : ℕ → S)
    (K : Kind S omega) (r : ℕ) (u : Fin r → S) (hu : ValidRoots K u)
    (he : Function.Injective fun s : S => s • ce S omega K r u 2 0) :
    RootRecurrence omega u := by sorry

end QAlgorithms.Papers.Independent.Support21.P12

end
