-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P16_proposition3_4
-- name    : QAlgorithms.Papers.Independent.Next46.P16.proposition3_4
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:05:32.856985+00:00
-- url     : https://prove2.me/theorems/b778a104-3b87-418a-9a19-22ef82af3007
-- title:
--   Polynomial sandwiches have unique bounded extensions and define the topology
-- statement:
--   Fix $N\ge1$, let $\mathcal H=L^2(\mathbb R^N)$, and let $T\in\mathcal S(\mathcal H)$. For every pair of finite polynomials $f_L,f_R$ in the canonical position and momentum operators, the ordered composition $f_L(Q,P)T f_R(Q,P)$ is defined on all Schwartz vectors and has a unique bounded extension $B_{T,f_L,f_R}$ to $\mathcal H$. The form bound is finite and satisfies
--   $$
--   \sup_{\psi,\varphi\in\mathcal S(\mathbb R^N),\ \|\psi\|_2,\|\varphi\|_2\le1}
--   |\langle f_L(Q,P)^*\psi,T f_R(Q,P)\varphi\rangle|
--   =\|B_{T,f_L,f_R}\|.
--   $$
--   As $f_L,f_R$ range over all such polynomials, these extension norms induce the original topology of $\mathcal S(\mathcal H)$. The statement retains both existence and uniqueness of the extension and equality of the two topologies.
-- source:
--   Schwartz operators, arXiv:1503.04086v1, PDF p. 12, Proposition 3.4

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P16

noncomputable section

open MeasureTheory Filter

open QAlgorithms.Papers.Independent.Claimed50.P10 (Configuration)

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsTraceClass)

open scoped BigOperators ENNReal ComplexOrder

namespace QAlgorithms.Papers.Independent.Next46.P16

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P16.canonicalComplexCalculus

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P16.canonicalRealCalculus

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P16.canonicalRealNonUnitalCalculus

/-- Proposition 3.4(a,b), PDF p.12: each ordered polynomial sandwich is defined
on all Schwartz functions, has a unique bounded extension, and its extension
norms induce the original Schwartz-operator topology. The final equality
identifies the form supremum used to construct polynomialTopology with that norm. -/
theorem proposition3_4 (n : ℕ) (hn : 0 < n) :
    (∀ (T : SchwartzOperator n) (pL pR : CanonicalPolynomial n),
      BddAbove (polynomialFormValues T.val pL pR) ∧
      ∃! B : CanonicalOperator n,
        (∀ f : Schwartz n, ∃ g : Schwartz n,
          schwartzToHilbert g = T.val (schwartzToHilbert (canonicalAction pR f)) ∧
          B (schwartzToHilbert f) = schwartzToHilbert (canonicalAction pL g)) ∧
        sSup (polynomialFormValues T.val pL pR) = ‖B‖) ∧
    schwartzOperatorTopology n = polynomialTopology n := by sorry

end QAlgorithms.Papers.Independent.Next46.P16

end
