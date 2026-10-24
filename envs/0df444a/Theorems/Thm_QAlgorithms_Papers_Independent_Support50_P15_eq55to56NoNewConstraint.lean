-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P15_eq55to56NoNewConstraint
-- name    : QAlgorithms.Papers.Independent.Support50.P15.eq55to56NoNewConstraint
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:51:37.998717+00:00
-- url     : https://prove2.me/theorems/44a06d36-7f34-455f-8f41-d9fc961b9721
-- title:
--   eq55 56 no new constraint
-- statement:
--   Let $d\ge2$ and $-\log d\le\Delta\le0$. The sharp bound satisfies
--
--   $$M(\Delta,d)\le-\Delta,$$
--
--   with equality exactly at $\Delta=-\log d$ and $\Delta=0$, and strict inequality throughout the interior. This is the new numerical observation explaining why the bound adds no constraint to the standard mutual-information identities $I(A:B)=S(A)+S(B)-S(AB)=D(\rho_{AB}\|\rho_A\otimes\rho_B)=-\Delta$. Those identities are background. The repeated $S(A)$ in the source prose is corrected by the displayed Eq. (55).
-- source:
--   Tight bound on relative entropy by entropy difference, arXiv:1304.0036v3, PDF p. 16, eq55-56-no-new-constraint

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P15

noncomputable section

attribute [local instance] Classical.propDecidable

open scoped Matrix ComplexConjugate ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Support50.P15

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

/-- Numerical observation after (55)--(56), PDF p.16. The prose MI typo is not redefined:
the correct identity uses S(A)+S(B)-S(AB), as the displayed equations require. -/
theorem eq55to56NoNewConstraint {d : ℕ} (hd : 2 ≤ d) (delta : ℝ)
    (hdelta : delta ∈ Set.Icc (-Real.log d) 0) :
    tightBound d delta ≤ (-delta : ℝ) ∧
    (tightBound d delta = (-delta : ℝ) ↔ delta = -Real.log d ∨ delta = 0) ∧
    (delta ∈ Set.Ioo (-Real.log d) 0 → tightBound d delta < (-delta : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P15

end
