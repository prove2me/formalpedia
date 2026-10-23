-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P26_remark_2_9
-- name    : QAlgorithms.Papers.Independent.Information100.P26.remark_2_9
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T10:48:21.210981+00:00
-- url     : https://prove2.me/theorems/82872cda-9b5d-4de9-b7c1-f7dea7007d83
-- title:
--   Remark 2.9: CP composition closure and one-iterate criteria
-- statement:
--   Fix $d\ge1$. Each property $P$ in $\{\mathrm{EB},\mathrm{PPT},\text{2-copositive}\}$ is preserved by left and right composition with every CP map: if $P(\phi)$ and $\psi$ is CP, then $P(\psi\phi)$ and $P(\phi\psi)$. Consequently, for every CP map $\phi$,
--   $$\phi\text{ is eventually }P\quad\Longleftrightarrow\quad\exists n_0\ge1:\ P(\phi^{n_0}).$$
--   Maps need not preserve trace. No immediate-successor closure statement is asserted for MTD.
-- source:
--   A complete characterization of eventually entanglement breaking unital quantum channels, arXiv:2609.24168v1, PDF p. 6, Remark 2.9

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Information100.P26.unitaryMeasurable

/-- arXiv:2609.24168v1, Remark 2.9, PDF pp.6. -/
theorem remark_2_9 {d : ℕ} (hd : 0 < d) :
    (∀ f g : Map d, CP g →
      (EB f → EB (g*f) ∧ EB (f*g)) ∧
      (PPT f → PPT (g*f) ∧ PPT (f*g)) ∧
      (TwoCopositive f → TwoCopositive (g*f) ∧ TwoCopositive (f*g))) ∧
    (∀ f : Map d, CP f →
      (Eventually EB f ↔ ∃ n : ℕ, 1 ≤ n ∧ EB (f^n)) ∧
      (Eventually PPT f ↔ ∃ n : ℕ, 1 ≤ n ∧ PPT (f^n)) ∧
      (Eventually TwoCopositive f ↔ ∃ n : ℕ, 1 ≤ n ∧ TwoCopositive (f^n))) := by sorry

end QAlgorithms.Papers.Independent.Information100.P26

end
