-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P96_trivialBibundle_iff_centralSection
-- name    : QAlgorithms.Papers.Independent.Intake100.P96.trivialBibundle_iff_centralSection
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:56:43.601597+00:00
-- url     : https://prove2.me/theorems/ca23cdcf-6f2e-420a-beba-1eb639dc2f71
-- title:
--   A smooth principal bibundle is trivial exactly when it has a global central section
-- statement:
--   Let $H$ be a finite-dimensional real Lie group and $p:E\to M$ a smooth principal $H$-bibundle over a Hausdorff paracompact smooth manifold. Write $h\cdot e$ and $e\triangleleft h$ for its commuting left and right principal actions. Triviality means smooth isomorphism, preserving the base and both actions, with $M\times H$ carrying left and right multiplication. Then
--
--   $$E\cong M\times H\quad\Longleftrightarrow\quad\exists\,s:M\to E\text{ smooth},\quad p\circ s=\operatorname{id}_M,\quad h\cdot s(x)=s(x)\triangleleft h\quad(\forall h\in H,\ x\in M).$$
--
--   This criterion distinguishes triviality as a bibundle from triviality of its underlying left principal bundle.
-- source:
--   Nonabelian Bundle Gerbes, their Differential Geometry and Gauge Theory, arXiv:hep-th/0312154v2, PDF p. 4, Proposition 2: central sections characterize trivial bibundles

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P96

open scoped Manifold ContDiff

namespace QAlgorithms.Papers.Independent.Intake100.P96

universe u v w z

section Bundles

variable {m h e : ℕ} {M : Type u} {H : Type v} {E : Type w}

variable [TopologicalSpace M] [ChartedSpace (RealModel m) M]

variable [TopologicalSpace H] [ChartedSpace (RealModel h) H]

variable [TopologicalSpace E] [ChartedSpace (RealModel e) E]

variable [Group H]

/-- Proposition 2, PDF p. 4: a bibundle is trivial exactly when it admits
one smooth global central section. -/
theorem trivialBibundle_iff_centralSection
    (B : LeftPrincipalBundle m h e M H E) (R : RightPrincipalStructure B) :
    IsTrivialBibundle B R ↔ ∃ s : M → E, IsCentralSection B R s := by sorry

end Bundles

end QAlgorithms.Papers.Independent.Intake100.P96
