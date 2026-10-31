-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P96_bibundlePhi_unique_smoothAutomorphisms
-- name    : QAlgorithms.Papers.Independent.Intake100.P96.bibundlePhi_unique_smoothAutomorphisms
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:58:37.037981+00:00
-- url     : https://prove2.me/theorems/985a6758-37eb-40b5-970c-3d8cc733fda8
-- title:
--   The computed bibundle multiplier is the unique smooth automorphism family with (5)–(7)
-- statement:
--   For a smooth principal $H$-bibundle $E\to M$, let $\phi_e(h)$ be the unique left multiplier with $\phi_e(h)\cdot e=e\triangleleft h$. There is a unique family of smooth group automorphisms having these computed values. Evaluation is jointly smooth, every inverse is smooth, and for all $e\in E$ and $k,h\in H$, $$\phi_{k\cdot e}(h)=k\phi_e(h)k^{-1},\qquad \phi_{e\triangleleft k}(h)=\phi_e(khk^{-1}).$$ Multiplicativity is carried by the group-automorphism type.
-- source:
--   Nonabelian Bundle Gerbes, their Differential Geometry and Gauge Theory, arXiv:hep-th/0312154v2, PDF p. 5, §2, the phi map: forward construction (4)–(7)

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

/-- Forward half of the phi characterization, PDF p. 5, (4)–(7).
The family is the computed left multiplier phiValue, uniquely packaged as
smooth group automorphisms. Both equivariance laws are conclusions. -/
theorem bibundlePhi_unique_smoothAutomorphisms
    (B : LeftPrincipalBundle m h e M H E) (R : RightPrincipalStructure B) :
    ∃! phi : E → MulAut H,
      (∀ q : E, ∀ k : H, phi q k = phiValue B R q k) ∧
      ContMDiff ((realModel e).prod (realModel h)) (realModel h) ∞
        (fun q : E × H => phi q.1 q.2) ∧
      (∀ q : E, ContMDiff (realModel h) (realModel h) ∞ (phi q).symm) ∧
      (∀ q : E, ∀ k l : H,
        phi (B.leftAction k q) l = k * phi q l * k⁻¹) ∧
      (∀ q : E, ∀ k l : H,
        phi (R.rightAction q k) l = phi q (k * l * k⁻¹)) := by sorry

end Bundles

end QAlgorithms.Papers.Independent.Intake100.P96
