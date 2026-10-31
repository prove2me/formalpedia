-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P06_strictReplacement
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P06.strictReplacement
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T22:46:52.509999+00:00
-- url     : https://prove2.me/theorems/e8e75744-1da0-49c5-9143-01714bd7554d
-- title:
--   Every Gr-category has a strict replacement
-- statement:
--   Let $\mathcal C$ be any Gr-category. There exists a Gr-category $\mathcal D$ and a strong monoidal equivalence with monoidal unit and counit such that
--
--   $$
--   \mathcal C\simeq_{\otimes}\mathcal D,\qquad
--   \alpha^{\mathcal D}_{x,y,z}=\mathrm{id},\quad
--   \lambda^{\mathcal D}_{x}=\mathrm{id},\quad
--   \varrho^{\mathcal D}_{x}=\mathrm{id}.
--   $$
--
--   The identity assertions include equality of their source and target objects. Object inverses in $\mathcal D$ are still required only up to isomorphism, and no skeletal condition is imposed. This is the source's strictification theorem under its stated notion of strictness.
-- source:
--   Hoàng Xuân Sính's Thesis: Categorifying Group Theory, arXiv:2308.05119v2, PDF p. 19, Appendix A, Theorem 14: strict replacement

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P06

namespace QAlgorithms.Papers.Independent.Intakenext100.P06

open CategoryTheory CategoryTheory.MonoidalCategory

open QAlgorithms.Papers.Independent.Gap48.P14

open QAlgorithms.Papers.Independent.Renew46.P18

universe u v u1 v1 w

attribute [local instance] QAlgorithms.Papers.Independent.Intakenext100.P06.singletonSymmetric

/-- Theorem 14, PDF p. 19 (also Section 4, p. 9): strict replacement,
with no skeletal requirement and no strict inverse requirement. -/
theorem strictReplacement {C : Type u} [Category.{v} C]
    [MonoidalCategory C] (h : IsWeakTwoGroup C) :
    ∃ (D : Type u) (cat : Category.{v} D),
      letI := cat
      ∃ m : MonoidalCategory D,
        letI := m
        IsWeakTwoGroup D ∧ StrictCoherence D ∧ Nonempty (GrEquivalence C D) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P06
