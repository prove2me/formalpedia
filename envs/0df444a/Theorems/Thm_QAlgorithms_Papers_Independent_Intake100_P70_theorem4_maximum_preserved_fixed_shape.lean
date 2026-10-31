-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P70_theorem4_maximum_preserved_fixed_shape
-- name    : QAlgorithms.Papers.Independent.Intake100.P70.theorem4_maximum_preserved_fixed_shape
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:35:37.193111+00:00
-- url     : https://prove2.me/theorems/2f982798-c82b-4444-b530-fdf34c12ea4b
-- title:
--   Theorem 4: maximum preserved codes are fixed-state sets up to isometry
-- statement:
--   Let $\mathcal E$ be a CPTP map between finite-dimensional nonzero complex Hilbert spaces, and let $C$ be a convex set of positive matrices of ordinary trace one. Preservation means equality of $\|\mathcal E(p\rho-(1-p)\sigma)\|_1$ and $\|p\rho-(1-p)\sigma\|_1$ for every $\rho,\sigma\in C$ and $p\in[0,1]$. Maximum means that no code satisfying the same criterion has a proper subset 1-isometric to $C$. A 1-isometry is a complex-linear identification of the code spans that maps the normalized state sets bijectively and preserves every weighted trace-norm distance. For every maximum preserved $C$, some CPTP map $\mathcal R$ from output to input satisfies
--
--   $$C\simeq_1\operatorname{Fix}(\mathcal R\circ\mathcal E)_+.$$
--
--   This connects the entire preserved-code shape to a fixed-state set on the original input space.
-- source:
--   Information preserving structures: A general framework for quantum zero-error information, arXiv:1006.1358v1, PDF p. 8, Theorem 4: maximum preserved codes are fixed-state sets up to isometry

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

/-- PDF pp.8,22, Theorem 4. Recovery returns to the input space even if the
channel changes dimension. Its entire fixed-state set has the code's shape. -/
theorem theorem4_maximum_preserved_fixed_shape {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [Nonempty I] [Nonempty J]
    (E : Superop I J) (hE : IsChannel E) (C : Set (Op I))
    (hC : MaximumCode (Preserved E) C) :
    ∃ R : Superop J I, IsChannel R ∧ OneIsometric C (fixedStates (R ∘ E)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P70

end
