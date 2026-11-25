-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__mul_sqrt_div_mul_sqrt_div_le_a87fee8277d6
-- name    : P2M_Formalism_MainNotions_BridgeLemma__mul_sqrt_div_mul_sqrt_div_le_a87fee8277d6
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:59:42.451299+00:00
-- url     : https://prove2.me/theorems/6bbf9f20-f329-4940-b003-7d9f4e111b32
-- title:
--   P2 M Formalism Main Notions Bridge Lemma  mul sqrt div mul sqrt div le a87fee8277d6: P2 M Formalism Main Notions Bridge Lemma  mul sqrt div mul sqrt div le a87fee8277d6
-- statement:
--   The P2 M Formalism Main Notions Bridge Lemma  mul sqrt div mul sqrt div le a87fee8277d6 construction uses the P2 M Formalism Main Notions Bridge Lemma  mul sqrt div mul sqrt div le a87fee8277d6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/RowsOneN.lean#L45-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/RowsOneN.lean#L45-L131

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_RowsNum
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_RowsOneN
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemma₂
set_option maxHeartbeats 800000

theorem P2M_Formalism_MainNotions_BridgeLemma__mul_sqrt_div_mul_sqrt_div_le_a87fee8277d6 {P σ₁ σ₂ hS₁ hS₂ h4₁ h4₂ hV₁ hV₂ cS c4 cV Γ Ex a2 a4 dq τ Q n₁ n₂ K4 N L₁ L₂ e : ℝ}
    (hP : 1 ≤ P) (hσ₁ : 1 ≤ σ₁) (hσ₂ : 1 ≤ σ₂)
    (hS1₁ : 1 ≤ hS₁) (hS1₂ : 1 ≤ hS₂) (h41₁ : 1 ≤ h4₁) (h41₂ : 1 ≤ h4₂) (hV1₁ : 1 ≤ hV₁) (hV1₂ : 1 ≤ hV₂)
    (hSP₁ : hS₁ ≤ P * σ₁ ^ 4) (hSP₂ : hS₂ ≤ P * σ₂ ^ 4) (h4P₁ : h4₁ ≤ P * σ₁ ^ 4) (h4P₂ : h4₂ ≤ P * σ₂ ^ 4)
    (hVP₁ : hV₁ ≤ P * σ₁ ^ 4) (hVP₂ : hV₂ ≤ P * σ₂ ^ 4) (hcS : 0 ≤ cS) (hc4 : 0 ≤ c4) (hcV : 0 ≤ cV)
    (hΓ : 0 ≤ Γ) (hEx : 0 ≤ Ex) (hτ : 0 ≤ τ) (hQ : 0 ≤ Q) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hK4 : 0 ≤ K4)
    (hN₁ : N ≤ hS₁ ^ cS * n₁ * (K4 * (h4₁ * h4₂) ^ c4)) (hN₂ : N ≤ hS₂ ^ cS * n₂ * (K4 * (h4₂ * h4₁) ^ c4))
    (hL₁ : L₁ = (hV₁ ^ cV) ^ 2 * (Γ * σ₁ ^ a2) * (Ex * σ₁ ^ a4) ^ 2 * τ * Q * σ₁ ^ (-dq))
    (hL₂ : L₂ = (hV₂ ^ cV) ^ 2 * (Γ * σ₂ ^ a2) * σ₂ ^ (-dq) * τ)
    (he : 4 * c4 + 4 * cS + 4 * cV + a2 / 2 + |a4| - dq / 2 ≤ -e) :
    N * (Real.sqrt (L₁ / n₁) * Real.sqrt (L₂ / n₂)) ≤
      (K4 * ((P ^ c4) ^ 2 * (P ^ cS) ^ 2 * (P ^ cV) ^ 2) * Γ * Ex * τ * Real.sqrt Q) * (σ₁ ^ (-e) * σ₂ ^ (-e)) := by sorry

alias «Formalism».«MainNotions».«BridgeLemma₂».«mul_sqrt_div_mul_sqrt_div_le» := P2M_Formalism_MainNotions_BridgeLemma__mul_sqrt_div_mul_sqrt_div_le_a87fee8277d6
