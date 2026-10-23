-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P19_hankel_six_not_extreme
-- name    : QAlgorithms.Papers.Independent.Information100.P19.hankel_six_not_extreme
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T09:47:51.803174+00:00
-- url     : https://prove2.me/theorems/4d4f0837-6f84-4b05-9136-1ca7a3d519c6
-- title:
--   Proposition 3.9
-- statement:
--   For $\Delta_{15}=p_1p_5-p_3^2=[51]-[33]$,
--   $$\Delta_{15}\in I_6^{\rm psd}\setminus I_6^{\rm all},\qquad
--   \mathbb R_{\ge0}\Delta_{15}\text{ is not extremal in }I_6^{\rm psd}.$$
--   Thus not every PSD Hankel-type inequality generates an extremal ray.
--
--   For a partition $\lambda$, the symbol $[\lambda]$ denotes a formal basis element evaluated as $\prod_j\operatorname{Tr}(X^{\lambda_j})$. Distinct formal coefficients are not identified by any fixed-dimensional trace identity.
-- source:
--   Optimal entanglement criteria from trace invariants, arXiv:2609.29471v1, PDF p. 19, Proposition 3.9

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

noncomputable section

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P19

/-- Proposition 3.9; arXiv:2609.29471v1, PDF pp.19. -/
theorem hankel_six_not_extreme  :
    b51-b33 ∈ psdCone 6 ∧ b51-b33 ∉ allCone 6 ∧ ¬ Extreme (psdCone 6) (b51-b33) := by sorry

end QAlgorithms.Papers.Independent.Information100.P19

end
