-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P46_four_types
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P46.four_types
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:03:50.026343+00:00
-- url     : https://prove2.me/theorems/68fe5415-0cee-4bab-a307-f6e26a991c43
-- title:
--   §5: four covariance types and the operational diagonalizations
-- statement:
--   For a physical standard two-mode covariance let $\alpha_q=\begin{pmatrix}a&c_1\\c_1&b\end{pmatrix}$, $\alpha_p=\begin{pmatrix}a&-c_2\\-c_2&b\end{pmatrix}$, with $c_1,c_2>0$. Select the symmetric chart first if $a=b$. Otherwise compare $A=a/b+b/a$ and $C=c_1/c_2+c_2/c_1$: type I has $A>C$, type II has $A<C$, and type III has $A=C$. In type I the local squeeze parameter and the subsequent two-mode squeeze satisfy
--   $$x=\sqrt{\frac{ac_1-bc_2}{ac_2-bc_1}}>0,\qquad \tanh(2r)=\frac{-2\sqrt{(ac_1-bc_2)(ac_2-bc_1)}}{|a^2-b^2|}.$$
--   In type II they satisfy
--   $$x=\sqrt{\frac{ac_1-bc_2}{bc_1-ac_2}}>0,\quad \tan(2\theta)=\frac{2\sqrt{(ac_1-bc_2)(bc_1-ac_2)}}{a^2-b^2}\operatorname{sign}(bc_1-ac_2).$$
--   Here $X(x)$ has diagonal $(\sqrt x,1/\sqrt x,1/\sqrt x,\sqrt x)$; applying $R(r)\oplus R(-r)$ or $\Theta(\theta)\oplus\Theta(\theta)$ after $X(x)$ diagonalizes the covariance. The rotation has rows $(\cos\theta,\sin\theta)$ and $(-\sin\theta,\cos\theta)$, and $R$ has diagonal $\cosh r$ and off-diagonal $\sinh r$. In type III, $a/b=c_1/c_2$ or $a/b=c_2/c_1$, and a block symplectic Williamson transformation exists. In the symmetric chart the explicit transformation of Eqs. (12)–(14) applies. This classifies the operational charts without claiming their unprioritized predicates are disjoint. In both generic cases there are further positive local squeeze parameters $x^{\prime},y$ for which $Y(y)X(x^{\prime})$ converts the resulting diagonal covariance to $\operatorname{diag}(\gamma_A,\gamma_B,\gamma_A,\gamma_B)$, with $\gamma_A,\gamma_B\ge\tfrac12$. Thus the operations give the full normal form, including the final local normalization.
-- source:
--   Gaussian relative entropy of entanglement, arXiv:quant-ph/0402109v3, PDF p. 8, §5: four covariance types and the operational diagonalizations

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P46

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P46

open scoped BigOperators ENNReal ComplexOrder Matrix

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsSeparable)

open QAlgorithms.Papers.Independent.Dependency50.P13
  (finiteRelativeEntropy compression entropyWeight)

open QAlgorithms.Papers.Independent.Claimed50.P47
  (Occupation bipartiteCharacteristic bipartiteWeyl gaussianStateCharacteristic)

-- These accepted definitions have the same completed Hilbert-space meaning.

open QAlgorithms.Papers.Independent.Next46.P13 (coordinateBasis)

open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff boundedOperator)

open QAlgorithms.Papers.Independent.Claimed50.P41 (IsDiagonal)

/-- Chen, PDF pp.8–9, (36): four covariance charts and operational
squeeze/rotation diagonalizations. Ratio predicates overlap at symmetry; the
symmetric chart is selected first. Inverse formulas never run at a=b. -/
theorem four_types (a b c1 c2 : ℝ) (hphysical : IsPhysicalCovariance (standardCM a b c1 c2))
    (hc1 : 0 < c1) (hc2 : 0 < c2) :
    covarianceType a b c1 c2 ∈ ({1, 2, 3, 4} : Set ℕ) ∧
    (a = b →
      let S := symplecticLift (symmetricSq (2 * a) (2 * c1) (2 * c2))
      standardCM a b c1 c2 = S * normalDiagonal
        (symmetricGammas (2 * a) (2 * c1) (2 * c2)) * S.transpose) ∧
    (a ≠ b → c1 / c2 + c2 / c1 < a / b + b / a →
      let x := Real.sqrt ((a * c1 - b * c2) / (a * c2 - b * c1))
      0 < x ∧ ∃ r : ℝ,
        Real.tanh (2 * r) = -2 * Real.sqrt ((a * c1 - b * c2) *
          (a * c2 - b * c1)) / |a ^ 2 - b ^ 2| ∧
        IsDiagonal (congruence (squeezeBoth r * xSqueeze x) (standardCM a b c1 c2)) ∧
        ∃ (xp y : ℝ) (g : Two → ℝ), 0 < xp ∧ 0 < y ∧ (∀ j, 1 / 2 ≤ g j) ∧
          congruence (ySqueeze y * xSqueeze xp * squeezeBoth r * xSqueeze x)
            (standardCM a b c1 c2) = normalDiagonal g) ∧
    (a ≠ b → a / b + b / a < c1 / c2 + c2 / c1 →
      let x := Real.sqrt ((a * c1 - b * c2) / (b * c1 - a * c2))
      0 < x ∧ ∃ t : ℝ,
        Real.tan (2 * t) = 2 * Real.sqrt ((a * c1 - b * c2) *
          (b * c1 - a * c2)) / (a ^ 2 - b ^ 2) * (if 0 < b * c1 - a * c2 then 1 else -1) ∧
        IsDiagonal (congruence (rotateBoth t * xSqueeze x) (standardCM a b c1 c2)) ∧
        ∃ (xp y : ℝ) (g : Two → ℝ), 0 < xp ∧ 0 < y ∧ (∀ j, 1 / 2 ≤ g j) ∧
          congruence (ySqueeze y * xSqueeze xp * rotateBoth t * xSqueeze x)
            (standardCM a b c1 c2) = normalDiagonal g) ∧
    (a ≠ b → a / b + b / a = c1 / c2 + c2 / c1 →
      (a / b = c1 / c2 ∨ a / b = c2 / c1) ∧
      ∃ (Sq : Matrix Two Two ℝ) (g : Two → ℝ),
        IsSymplecticMatrix (symplecticLift Sq) ∧ (∀ j, 1 / 2 ≤ g j) ∧
        standardCM a b c1 c2 = symplecticLift Sq * normalDiagonal g * (symplecticLift Sq).transpose) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P46

end
