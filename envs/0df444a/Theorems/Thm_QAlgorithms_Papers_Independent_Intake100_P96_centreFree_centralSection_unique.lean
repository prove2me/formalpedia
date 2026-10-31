-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P96_centreFree_centralSection_unique
-- name    : QAlgorithms.Papers.Independent.Intake100.P96.centreFree_centralSection_unique
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:59:02.691674+00:00
-- url     : https://prove2.me/theorems/437233b3-0d96-4a55-a271-9d85235baf27
-- title:
--   For a centre-free group a global central section is unique when it exists
-- statement:
--   Let $E\to M$ be a smooth principal $H$-bibundle with $Z(H)=\{1\}$. If $s,t:M\to E$ are smooth global central sections, then $$s=t.$$ This is uniqueness conditional on existence; it does not assert every bibundle is trivial.
-- source:
--   Nonabelian Bundle Gerbes, their Differential Geometry and Gauge Theory, arXiv:hep-th/0312154v2, PDF p. 5, §2, uniqueness sentence before Proposition 3

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

/-- Uniqueness sentence before Proposition 3, PDF p. 5.
Centre-freeness gives at most one smooth global central section; existence
is supplied separately by the triviality criterion. -/
theorem centreFree_centralSection_unique
    (B : LeftPrincipalBundle m h e M H E) (R : RightPrincipalStructure B)
    (centreFree : ∀ k : H, (∀ l : H, k * l = l * k) → k = 1) :
    ∀ s t : M → E, IsCentralSection B R s → IsCentralSection B R t →
      s = t := by sorry

end Bundles

end QAlgorithms.Papers.Independent.Intake100.P96
