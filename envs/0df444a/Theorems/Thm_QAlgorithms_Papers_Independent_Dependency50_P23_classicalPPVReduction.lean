-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P23_classicalPPVReduction
-- name    : QAlgorithms.Papers.Independent.Dependency50.P23.classicalPPVReduction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:38:00.663858+00:00
-- url     : https://prove2.me/theorems/c0f81c0c-d510-49d1-a5bb-73fbed38f895
-- title:
--   Proposition 9: classical reduction to PPV, corrected logarithm
-- statement:
--   Let $W(y|x)$ be a classical channel on nonempty finite input and output alphabets: $W(y|x)\ge0$ and $\sum_yW(y|x)=1$. Fix $0\le e<1$, and let $R_{\mathrm{PPV}}^{\mathrm{messages}}$ be the attained maximum of $\sum_xs_x$ subject to $s_x\ge0$, $0\le Q_{xy}\le s_x$, $\sum_xQ_{xy}\le1$, and $\sum_{x,y}W(y|x)Q_{xy}\ge(1-e)\sum_xs_x$. Then
--
--   $$C_{\mathrm{NS}}^{(1)}(W,e)=C_{\mathrm{NS}\cap\mathrm{PPT}}^{(1)}(W,e)=\log_2R_{\mathrm{PPV}}^{\mathrm{messages}}(W,e).$$
--
--   This corrects the units in printed Eq.(39): Eq.(38) defines a message number, whereas capacities are in bits. Positivity is inherited from Eq.(35). For the noiseless binary channel at zero error the message number is two and the capacity is one bit. Round 1 independently verified this correction.
-- source:
--   Semidefinite programming strong converse bounds for classical capacity, arXiv:1610.06381v4, PDF p. 14, Proposition 9

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P23

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P23

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

open QAlgorithms.Papers.Independent.Information100.P80 (log2 quantumCapacity)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

variable {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

/-- PDF pp.13–14, Proposition 9, CORRECTED UNITS: Eq.(38) is a message number,
so Eq.(39) needs log2 of that number, as confirmed by Eq.(40). Nonnegativity is
inherited from Eq.(35). On the binary identity at e=0, LP=2 and capacity=1.
This correction requires independent moderation; see HARD.md. -/
theorem classicalPPVReduction [Nonempty A] [Nonempty B] (W : A → B → ℝ)
    (hW0 : ∀ x y, 0 ≤ W x y) (hW1 : ∀ x, ∑ y, W x y = 1)
    (e : ℝ) (he0 : 0 ≤ e) (he1 : e < 1) :
    oneShot false (QAlgorithms.Papers.Independent.Information100.P62.classicalChannel (fun y x => W x y)) e = oneShot true (QAlgorithms.Papers.Independent.Information100.P62.classicalChannel (fun y x => W x y)) e ∧
    oneShot false (QAlgorithms.Papers.Independent.Information100.P62.classicalChannel (fun y x => W x y)) e = log2 (sSup (ppvValues W e)) ∧
    IsGreatest (ppvValues W e) (sSup (ppvValues W e)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P23

end
