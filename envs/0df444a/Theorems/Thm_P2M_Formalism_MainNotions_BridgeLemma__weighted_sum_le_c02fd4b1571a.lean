-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__weighted_sum_le_c02fd4b1571a
-- name    : P2M_Formalism_MainNotions_BridgeLemma__weighted_sum_le_c02fd4b1571a
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:59:36.940807+00:00
-- url     : https://prove2.me/theorems/78ac37fd-c547-4258-baf9-96974683552b
-- title:
--   P2 M Formalism Main Notions Bridge Lemma  weighted sum le c02fd4b1571a: P2 M Formalism Main Notions Bridge Lemma  weighted sum le c02fd4b1571a
-- statement:
--   The P2 M Formalism Main Notions Bridge Lemma  weighted sum le c02fd4b1571a construction uses the P2 M Formalism Main Notions Bridge Lemma  weighted sum le c02fd4b1571a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/RowsFibres.lean#L22-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/RowsFibres.lean#L22-L53

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubgroupsOfIndexLe
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_RowsRpowPow
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_RowsFibres
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemma₂
open Formalism.HermitianLatticeCounting
open Classical

theorem P2M_Formalism_MainNotions_BridgeLemma__weighted_sum_le_c02fd4b1571a {Pr κ : Type} (S : Finset Pr) (w a₁ a₂ : Pr → ℝ) (c₁ c₂ : Pr → κ) (M R Φ : ℝ) (N : κ → κ → ℝ)
    (α φ : κ → ℝ) (hM : 0 ≤ M) (hR : 0 ≤ R) (hw : ∀ p ∈ S, 0 ≤ w p) (ha₁ : ∀ p ∈ S, 0 ≤ a₁ p) (ha₂ : ∀ p ∈ S, 0 ≤ a₂ p)
    (hα₁ : ∀ p ∈ S, a₁ p ≤ α (c₁ p)) (hα₂ : ∀ p ∈ S, a₂ p ≤ α (c₂ p))
    (hcount : ∀ x ∈ S.image c₁, ∀ y ∈ S.image c₂, ∑ p ∈ S.filter (fun p => c₁ p = x ∧ c₂ p = y), w p ≤ M * N x y)
    (hN : ∀ x ∈ S.image c₁, ∀ y ∈ S.image c₂, N x y * (α x * α y) ≤ R * (φ x * φ y))
    (hα0 : ∀ x, 0 ≤ α x) (hφ0 : ∀ x, 0 ≤ φ x)
    (hΦ₁ : ∑ x ∈ S.image c₁, φ x ≤ Φ) (hΦ₂ : ∑ y ∈ S.image c₂, φ y ≤ Φ) :
    ∑ p ∈ S, w p * (a₁ p * a₂ p) ≤ M * (R * Φ ^ 2) := by sorry

alias «Formalism».«MainNotions».«BridgeLemma₂».«weighted_sum_le» := P2M_Formalism_MainNotions_BridgeLemma__weighted_sum_le_c02fd4b1571a
