-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P35_sandwichedTrace_derivative
-- name    : QAlgorithms.Papers.Independent.Dependency50.P35.sandwichedTrace_derivative
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:10:29.606053+00:00
-- url     : https://prove2.me/theorems/834dd945-d2c6-4ee3-9d77-db780998f77a
-- title:
--   Proposition 15: derivative of the sandwiched trace
-- statement:
--   Let $X,Y>0$ be finite-dimensional complex operators and set $Z_\alpha=Y^{(1-\alpha)/(2\alpha)}XY^{(1-\alpha)/(2\alpha)}$ and $f(\alpha)=\operatorname{Tr}(Z_\alpha^\alpha)$. For every $\alpha>0$, $f$ is differentiable and
--
--   $$
--   f'(\alpha)=\operatorname{Tr}(Z_\alpha^\alpha\ln Z_\alpha)-\frac1\alpha\operatorname{Tr}(Z_\alpha^\alpha\ln Y),\qquad
--   f'(1)=\operatorname{Tr}[X(\ln X-\ln Y)].
--   $$
--
--   The natural logarithms and trace factor are fixed by the derivation on PDF p.20: the printed first expression uses log instead of ln, and the printed specialization omits $\operatorname{Tr}X$. In base two the last expression is $(\ln2)(\operatorname{Tr}X)D_1(X\|Y)$. This correction preserves the general unnormalized hypothesis.
-- source:
--   On quantum Renyi entropies: a new generalization and some properties, arXiv:1306.3142v4, PDF p. 18, Proposition 15

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Dependency50.P35

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the accepted matrix type and positive-operator Schatten expression.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat schatten)

open QAlgorithms.Papers.Independent.Information100.P58 (Distribution)

/-- PDF pp.18–20, Proposition 15, corrected from its derivation p.20:
the general formula uses ln Y, not log Y; at one the missing factor tr X is
restored by writing Tr[X(ln X-ln Y)]. For X=[2],Y=[1] this is 2 ln 2. -/
theorem sandwichedTrace_derivative {I : Type} [Fintype I] [DecidableEq I]
    (X Y : Mat I) (hX : X.PosDef) (hY : Y.PosDef) :
    (∀ a : ℝ, 0 < a → HasDerivAt (fun t : ℝ => rawTrace t X Y)
      (tr (spectralPower (sandwich a X Y) a * lnOp (sandwich a X Y)) -
        (1/a) * tr (spectralPower (sandwich a X Y) a * lnOp Y)) a) ∧
    HasDerivAt (fun t : ℝ => rawTrace t X Y) (tr (X * (lnOp X - lnOp Y))) 1 := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P35

end
