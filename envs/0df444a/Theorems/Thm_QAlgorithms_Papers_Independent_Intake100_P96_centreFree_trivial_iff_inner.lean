-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P96_centreFree_trivial_iff_inner
-- name    : QAlgorithms.Papers.Independent.Intake100.P96.centreFree_trivial_iff_inner
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:58:07.293565+00:00
-- url     : https://prove2.me/theorems/3dc3eee7-8366-4412-86d6-4bb9152fabd7
-- title:
--   Pointwise innerness characterizes triviality for a centre-free group
-- statement:
--   Let $H$ be a finite-dimensional real Lie group with trivial centre, and let $p:E\to M$ be a smooth principal $H$-bibundle over a Hausdorff paracompact smooth manifold. Define $\phi_e(h)$ as the unique element of $H$ satisfying $\phi_e(h)\cdot e=e\triangleleft h$. Then
--
--   $$E\cong M\times H\quad\Longleftrightarrow\quad\forall e\in E\ \exists k\in H\ \forall h\in H,\qquad\phi_e(h)=khk^{-1}.$$
--
--   The isomorphism on the left preserves both principal actions. The centre-free hypothesis is essential to this criterion; connectedness and compactness are not assumed.
-- source:
--   Nonabelian Bundle Gerbes, their Differential Geometry and Gauge Theory, arXiv:hep-th/0312154v2, PDF p. 5, Proposition 3: centre-free triviality criterion

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

/-- Proposition 3, PDF p. 5: pointwise innerness characterizes triviality
when the centre of H is trivial. Innerness uses the computed multiplier (4),
not a freely chosen automorphism family. The centre hypothesis quantifies
all group elements and is retained even when H is disconnected. -/
theorem centreFree_trivial_iff_inner
    (B : LeftPrincipalBundle m h e M H E) (R : RightPrincipalStructure B)
    (centreFree : ∀ k : H, (∀ l : H, k * l = l * k) → k = 1) :
    IsTrivialBibundle B R ↔
      ∀ q : E, ∃ k : H, ∀ l : H, phiValue B R q l = k * l * k⁻¹ := by sorry

end Bundles

end QAlgorithms.Papers.Independent.Intake100.P96
