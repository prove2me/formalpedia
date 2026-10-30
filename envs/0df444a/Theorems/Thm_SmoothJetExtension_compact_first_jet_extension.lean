-- Prove2me | Theorems.Thm_SmoothJetExtension_compact_first_jet_extension
-- name    : SmoothJetExtension.compact_first_jet_extension
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-29T20:32:00.069489+00:00
-- url     : https://prove2.me/theorems/4b2373e1-bd50-47e4-972d-d55aa54fe299
-- title:
--   Compactly supported smooth extension of compatible local first jets
-- statement:
--   Let E be a finite-dimensional real normed space, let C be compact, and prescribe scalar values h(p) and continuous linear functionals L(p) on C. Suppose each point of C has an open neighborhood carrying a smooth scalar function whose value and derivative agree with h and L throughout its intersection with C. Then there is a globally smooth, compactly supported scalar function H such that
--
--   $$H(p)=h(p),\qquad DH(p)=L(p)\quad(p\in C).$$
--
--   This glues actual compatible local first jets and preserves them under a compact cutoff. Arbitrary value and derivative assignments are not asserted to be extendible.
-- source:
--   Derived extension lemma for the contact Hamiltonian construction, Geiges Contact Geometry arXiv:math/0307242v2, proof of Theorem2.42 pp34–36 and affine prescribed-jet construction pp32–33. Formal gluing: Mathlib Geometry/Manifold/PartitionOfUnity.lean, SmoothPartitionOfUnity.exists_isSubordinate and contDiffAt_finsum. Compact cutoff: exists_contMDiffMap_one_nhds_of_subset_interior. Revision0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib
open Set Function
open scoped ContDiff

theorem SmoothJetExtension.compact_first_jet_extension {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (C : Set E) (hC : IsCompact C)
    (h : E → ℝ) (L : E → (E →L[ℝ] ℝ))
    (hloc : ∀ p ∈ C, ∃ U : Set E, IsOpen U ∧ p ∈ U ∧
      ∃ g : E → ℝ, ContDiffOn ℝ ∞ g U ∧
        ∀ q ∈ C ∩ U, g q = h q ∧ fderiv ℝ g q = L q) :
    ∃ H : E → ℝ, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧
      ∀ p ∈ C, H p = h p ∧ fderiv ℝ H p = L p := by sorry
