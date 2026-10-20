-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P35_schatten_variational
-- name    : QAlgorithms.Papers.Independent.Dependency50.P35.schatten_variational
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:07:46.500982+00:00
-- url     : https://prove2.me/theorems/b23e738e-9280-4c6e-9bc7-b8db3e145754
-- title:
--   Lemma 12: variational Schatten formula
-- statement:
--   Let $p>0$, $p\ne1$, and $q\in\mathbb R\setminus\{0,1\}$ satisfy $1/p+1/q=1$. For a PSD finite-dimensional operator $X$, write $\|X\|_p=(\operatorname{Tr}X^p)^{1/p}$. Then
--
--   $$
--   \|X\|_p=\sup_{Z\ge0,\ \operatorname{Tr}Z\le1}\operatorname{Tr}[XZ^{1/q}]\quad(p>1),\qquad
--   \|X\|_p=\inf_{Z\ge0,\ Z\gg X,\ \operatorname{Tr}Z\le1}\operatorname{Tr}[XZ^{1/q}]\quad(0<p<1).
--   $$
--
--   Here $Z\gg X$ means kernel inclusion, and negative powers use the generalized inverse. Both extrema are extended-real extrema asserted to equal the displayed finite real number, including $X=0$. The positivity of $p$ comes from the preceding definition.
-- source:
--   On quantum Renyi entropies: a new generalization and some properties, arXiv:1306.3142v4, PDF p. 14, Lemma 12

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Dependency50.P35

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the accepted matrix type and positive-operator Schatten expression.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat schatten)

open QAlgorithms.Papers.Independent.Information100.P58 (Distribution)

/-- PDF pp.14–15, Lemma 12: p>0 is inherited from the definition immediately
above the lemma. EReal extrema are asserted to equal a finite real value. -/
theorem schatten_variational {I : Type} [Fintype I] [DecidableEq I]
    (p q : ℝ) (hp : 0 < p) (hp1 : p ≠ 1) (hq0 : q ≠ 0) (hq1 : q ≠ 1)
    (hpq : 1/p + 1/q = 1) (X : Mat I) (hX : X.PosSemidef) :
    (1 < p → (schatten p X : EReal) =
      sSup {v : EReal | ∃ Z : Mat I, Z.PosSemidef ∧ tr Z ≤ 1 ∧
        v = (tr (X * spectralPower Z (1/q)) : EReal)}) ∧
    (p < 1 → (schatten p X : EReal) =
      sInf {v : EReal | ∃ Z : Mat I, Z.PosSemidef ∧ Dominates Z X ∧ tr Z ≤ 1 ∧
        v = (tr (X * spectralPower Z (1/q)) : EReal)}) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P35

end
