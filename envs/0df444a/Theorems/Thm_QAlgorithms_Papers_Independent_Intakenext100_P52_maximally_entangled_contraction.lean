-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P52_maximally_entangled_contraction
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P52.maximally_entangled_contraction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:30:48.292551+00:00
-- url     : https://prove2.me/theorems/7ea3dd5e-b536-478e-939d-51906fbaf3cb
-- title:
--   Lemma 1: maximally entangled contraction
-- statement:
--   Let $I$ be a nonempty finite computational basis of cardinality $d$, and let $|\alpha\rangle$ be a unit vector on this register. Put $|\phi\rangle=d^{-1/2}\sum_{i\in I}|i,i\rangle$. With registers ordered $1,2,3$, destructive contraction of the first two registers gives
--
--   $$ (\langle\phi|_{12}\otimes I_3)(|\alpha\rangle_1\otimes|\phi\rangle_{23})=d^{-1}|\alpha\rangle_3. $$
--
--   The factor $1/d$ is retained: this is the subnormalized branch vector, rather than its normalized conditional state.
-- source:
--   An introduction to measurement based quantum computation, arXiv:quant-ph/0508124v2, PDF p. 3, Lemma 1: maximally entangled contraction

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P52

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Intakenext100.P52

open QAlgorithms.Papers.Independent.Information100.P21 (Vec)

open QAlgorithms.Papers.Independent.Gap20.P01 (applyRect)

/-- Lemma 1, PDF p.3: the displayed output is a destructive bra contraction,
not a normalized conditional state or a projector retaining registers 1 and 2. -/
theorem maximally_entangled_contraction {I : Type*} [Fintype I] [Nonempty I] [DecidableEq I]
    (alpha : Vec I) (halpha : IsState alpha) :
    teleportContraction alpha (finiteMaxEntangled I) (finiteMaxEntangled I) =
      ((Fintype.card I : ℂ)⁻¹) • alpha := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P52

end
