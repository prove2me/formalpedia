-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P07_projector_formulation
-- name    : QAlgorithms.Papers.Independent.Information100.P07.projector_formulation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:38:30.547518+00:00
-- url     : https://prove2.me/theorems/c7986611-0da3-4116-84e1-efc86bb6c65a
-- title:
--   Unnumbered: projector formulation, Eqs. (5)–(6)
-- statement:
--   Let $\rho,\sigma$ be entangled two-qutrit states. At least one of the following holds: the states are LU equivalent; they have one-sided rank-two orthogonal flag decompositions with the same retained weight and LU-equivalent entangled states, allowing either party to hold the flag; or they have two-sided rank-two rectangular decompositions with the same retained weight, LU-equivalent entangled states, and separable exterior states on the complementary subspaces. This is equivalent to existence of admissible product projectors $R,R'$ with local ranks two or three and a product unitary $W$ satisfying
--   $$[\rho,R]=[\sigma,R']=0,\quad \rho-R\rho R,\ \sigma-R'\sigma R'\in\mathrm{SEP},\quad WRW^\dagger=R',\quad R'\sigma R'=W(R\rho R)W^\dagger.$$
--   Here all flag decompositions have $0<w<1$; weight one is included by LU equivalence.
--
--   The projectors select full retained blocks. This equivalence is algebraic and does not replace the separate operational classification theorem.
-- source:
--   Complete Classification of Reversible Entanglement Transformations of Two Qutrits, arXiv:2610.05234v1, PDF p. 3, Eqs. (5)–(6)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P07

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P07

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms QAlgorithms.Entanglement

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:2610.05234v1, PDF pp.3,17–18, Eqs.(5)–(6): the projector formulation of Cases 2–4. -/
theorem projector_formulation (rho sigma : Joint) (hr : Entangled rho) (hs : Entangled sigma) :
    CasesTwoThroughFour rho sigma ↔
    ∃ R S : Joint, ∃ U V : Matrix.unitaryGroup (Fin 3) ℂ,
      Admissible rho R ∧ Admissible sigma S ∧
      Matrix.kronecker (U : Local) (V : Local) * R * (Matrix.kronecker (U : Local) (V : Local))ᴴ = S ∧
      S * sigma * S = Matrix.kronecker (U : Local) (V : Local) * (R * rho * R) *
        (Matrix.kronecker (U : Local) (V : Local))ᴴ := by sorry

end QAlgorithms.Papers.Independent.Information100.P07

end
