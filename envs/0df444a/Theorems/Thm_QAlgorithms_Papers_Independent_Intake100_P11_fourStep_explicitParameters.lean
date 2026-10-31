-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P11_fourStep_explicitParameters
-- name    : QAlgorithms.Papers.Independent.Intake100.P11.fourStep_explicitParameters
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:52:45.323973+00:00
-- url     : https://prove2.me/theorems/2f442633-48b8-43a8-919f-33d3c8ebdbf3
-- title:
--   Explicit four-step synthesis and its nonsingular parameter chart
-- statement:
--   Let $M(t)=\begin{pmatrix}-t&-1\\1&0\end{pmatrix}$. For arbitrary real $k_1,k_2,k_3,k_4$,
--
--   $$
--   M(k_4)M(k_3)M(k_2)M(k_1)=
--   \begin{pmatrix}
--   k_4k_3k_2k_1-k_4k_3-k_2k_1-k_4k_1+1&k_4k_3k_2-k_4-k_2\\
--   -k_3k_2k_1+k_3+k_1&1-k_3k_2
--   \end{pmatrix}.
--   $$
--
--   For any target $S=\begin{pmatrix}a&b\\c&d\end{pmatrix}$ with $ad-bc=1$, there exists $k_1$ such that $c-dk_1\ne0$. For every such choice, set
--
--   $$
--   k_3=c-dk_1,\qquad k_2=\frac{1-d}{k_3},\qquad k_4=\frac{1-a+bk_1}{k_3}.
--   $$
--
--   The product equals $S$. Separately, the all-zero four-step word equals the identity. These formulas give exact ideal synthesis, with a free parameter that the source discusses using for noise optimization; no noise-optimization claim is included here.
-- source:
--   Universal linear Bogoliubov transformations through one-way quantum computation, arXiv:0910.0660v1, PDF p. 5, §III, Eqs.(5)–(6)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P11

noncomputable section

open scoped Matrix BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P11

/-- PDF p.5, Eqs.(5)--(6): full product, guarded rational synthesis chart,
existence of a valid chart for every target, and separate all-zero identity.
No 0/0 convention is used to justify the identity example. -/
theorem fourStep_explicitParameters :
    (∀ kappa1 kappa2 kappa3 kappa4 : ℝ,
      elementaryWord [kappa1, kappa2, kappa3, kappa4] =
        !![kappa4 * kappa3 * kappa2 * kappa1 - kappa4 * kappa3 -
              kappa2 * kappa1 - kappa4 * kappa1 + 1,
            kappa4 * kappa3 * kappa2 - kappa4 - kappa2;
            -kappa3 * kappa2 * kappa1 + kappa3 + kappa1,
            -kappa3 * kappa2 + 1]) ∧
    (∀ A : Mat2, IsOneModeSymplectic A →
      (∃ kappa1 : ℝ, A 1 0 - A 1 1 * kappa1 ≠ 0) ∧
      ∀ kappa1 : ℝ, A 1 0 - A 1 1 * kappa1 ≠ 0 →
        let kappa3 := A 1 0 - A 1 1 * kappa1
        let kappa2 := (1 - A 1 1) / kappa3
        let kappa4 := (1 - A 0 0 + A 0 1 * kappa1) / kappa3
        elementaryWord [kappa1, kappa2, kappa3, kappa4] = A) ∧
    elementaryWord [0, 0, 0, 0] = 1 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P11

end
