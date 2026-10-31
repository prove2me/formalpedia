-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P70_preserved_iff_exact_recovery
-- name    : QAlgorithms.Papers.Independent.Intake100.P70.preserved_iff_exact_recovery
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:50:28.997249+00:00
-- url     : https://prove2.me/theorems/479d327c-15ab-4cb1-b6bc-8c8f8ad1c7c4
-- title:
--   Unnumbered: the weak condition is equivalent to exact recoverability
-- statement:
--   Let $\mathcal E$ be a CPTP map between finite-dimensional nonzero complex Hilbert spaces, and let $C$ be a convex set of positive matrices of ordinary trace one. Preservation means equality of $\|\mathcal E(p\rho-(1-p)\sigma)\|_1$ and $\|p\rho-(1-p)\sigma\|_1$ for every $\rho,\sigma\in C$ and $p\in[0,1]$. For every such convex code, without a maximum assumption,
--
--   $$C\text{ is preserved}\iff\exists\mathcal R\text{ CPTP},\ \forall\rho\in C,\ \mathcal R\mathcal E(\rho)=\rho.$$
--
--   This is the unnumbered all-code conclusion on p.10, separate from the maximum-code Proposition 1 and Corollary 7.
-- source:
--   Information preserving structures: A general framework for quantum zero-error information, arXiv:1006.1358v1, PDF p. 10, Unnumbered: the weak condition is equivalent to exact recoverability

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P70

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Intake100.P70

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P21 (channelAdjoint)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart negativePart)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P34 (supportProjector)

/-- PDF p.10, unnumbered exact-recovery equivalence for ALL convex codes,
without a maximum hypothesis. One recovery works for every code state. -/
theorem preserved_iff_exact_recovery {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [Nonempty I] [Nonempty J]
    (E : Superop I J) (hE : IsChannel E) (C : Set (Op I)) (hC : IsCode C) :
    Preserved E C ↔ ∃ R : Superop J I, IsChannel R ∧ ∀ rho ∈ C, R (E rho) = rho := by sorry

end QAlgorithms.Papers.Independent.Intake100.P70

end
