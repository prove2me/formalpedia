-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P42_mixed_restriction_reasonable
-- name    : QAlgorithms.Papers.Independent.Intake100.P42.mixed_restriction_reasonable
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:24:53.831658+00:00
-- url     : https://prove2.me/theorems/c869f086-c18e-4f07-b783-20ad25040b3f
-- title:
--   Reasonableness and norm bounds for the projective-to-injective restriction
-- statement:
--   Let $X,Y,V,W$ be arbitrary normed spaces over the same real or complex field, and let $\alpha$ be any uniform crossnorm family. Write $\rho_{p,q}(L)$ for the actual induced norm of the canonical action of the algebraic operator tensor $L$, with domain norm $p$ and range norm $q$. Then $\rho_{\pi,\varepsilon}$ is a genuine reasonable crossnorm on $\mathcal B(X,V)\otimes\mathcal B(Y,W)$, and
--
--   $$\|L\|_\varepsilon\le\rho_{\pi,\varepsilon}(L)\le\rho_{\alpha,\alpha}(L)\le\|L\|_\pi.$$
--
--   The following endpoint consequences from the same source paragraph are also retained:
--
--   $$\|L\|_\varepsilon\le\rho_{\varepsilon,\varepsilon}(L),\qquad\rho_{\pi,\pi}(L)\le\|L\|_\pi.$$
--
--   All three extreme induced norms are finite. The extreme norms outside the restrictions are computed on the operator tensor product. No joint uniformity assumption for distinct norms is made.
-- source:
--   Restriction of Uniform Crossnorms, arXiv:2212.10780v2, PDF p. 7, Remark 4.3: reasonableness of the projective-to-injective restriction

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P42

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P42

open scoped TensorProduct ENNReal

open QAlgorithms.Papers.Independent.Next46.P02

universe u

variable {F : Type u} [RCLike F]

/-- PDF p.7, Remark 4.3 and its following paragraph: mixed restriction is a
reasonable crossnorm, the four-term chain holds for every uniform alpha, and
both endpoint restrictions satisfy the stated one-sided bounds. -/
theorem mixed_restriction_reasonable (a : CrossnormFamily F) (ha : IsUniform a)
    (X Y V W : Type u)
    [NormedAddCommGroup X] [NormedSpace F X]
    [NormedAddCommGroup Y] [NormedSpace F Y]
    [NormedAddCommGroup V] [NormedSpace F V]
    [NormedAddCommGroup W] [NormedSpace F W] :
    ReasonableCrossnorm
      (restrictedOperatorNorm (F := F) (X := X) (Y := Y) (V := V) (W := W)
        algebraicProjectiveNorm injectiveNorm) ∧
    (∀ L : TensorProduct F (X →L[F] V) (Y →L[F] W),
      injectiveNorm L ≤ restrictedOperatorNorm algebraicProjectiveNorm injectiveNorm L ∧
      restrictedOperatorNorm algebraicProjectiveNorm injectiveNorm L ≤
        restrictedOperatorNorm (a.norm X Y) (a.norm V W) L ∧
      restrictedOperatorNorm (a.norm X Y) (a.norm V W) L ≤ algebraicProjectiveNorm L ∧
      injectiveNorm L ≤ restrictedOperatorNorm injectiveNorm injectiveNorm L ∧
      restrictedOperatorNorm algebraicProjectiveNorm algebraicProjectiveNorm L ≤ algebraicProjectiveNorm L ∧
      extendedOperatorNorm algebraicProjectiveNorm injectiveNorm (operatorAction L) < ⊤ ∧
      extendedOperatorNorm injectiveNorm injectiveNorm (operatorAction L) < ⊤ ∧
      extendedOperatorNorm algebraicProjectiveNorm algebraicProjectiveNorm (operatorAction L) < ⊤) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P42

end
