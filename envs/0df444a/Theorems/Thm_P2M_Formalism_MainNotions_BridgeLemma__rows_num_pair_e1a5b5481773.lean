-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__rows_num_pair_e1a5b5481773
-- name    : P2M_Formalism_MainNotions_BridgeLemma__rows_num_pair_e1a5b5481773
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:06:05.672751+00:00
-- url     : https://prove2.me/theorems/2384373f-d34c-4810-9a69-abbb37ed977a
-- title:
--   P2 M Formalism Main Notions Bridge Lemma  rows num pair e1a5b5481773: P2 M Formalism Main Notions Bridge Lemma  rows num pair e1a5b5481773
-- statement:
--   The P2 M Formalism Main Notions Bridge Lemma  rows num pair e1a5b5481773 construction uses the P2 M Formalism Main Notions Bridge Lemma  rows num pair e1a5b5481773 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/RowsNum.lean#L32-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/RowsNum.lean#L32-L108

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_RowsNum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemma₂

theorem P2M_Formalism_MainNotions_BridgeLemma__rows_num_pair_e1a5b5481773 {P σ₁ σ₂ h₁ h₂ cr Γ a2 dq E1 F6 XiH XiP ck e l₁ l₂ : ℝ} (hP : 1 ≤ P) (hσ₁ : 1 ≤ σ₁) (hσ₂ : 1 ≤ σ₂)
    (h1₁ : 1 ≤ h₁) (h1₂ : 1 ≤ h₂) (hh₁ : h₁ ≤ P * σ₁ ^ 4) (hh₂ : h₂ ≤ P * σ₂ ^ 4) (hcr : 0 ≤ cr) (hΓ : 0 ≤ Γ)
    (hE1 : 0 ≤ E1) (hF6 : 0 ≤ F6) (hXiH : 0 ≤ XiH) (hXi : XiH ≤ XiP * (σ₁ * σ₂) ^ (4 * ck))
    (hl₁ : l₁ = (h₁ ^ cr) ^ 2 * (Γ * σ₁ ^ a2) * σ₁ ^ (-dq)) (hl₂ : l₂ = (h₂ ^ cr) ^ 2 * (Γ * σ₂ ^ a2) * σ₂ ^ (-dq))
    (he : 4 * ck + 4 * E1 + 4 * cr + a2 / 2 - dq / 2 ≤ -e) :
    XiH * ((h₁ * h₂) ^ E1 * F6) * Real.sqrt (l₁ * l₂) ≤
      XiP * ((P ^ E1) ^ 2 * (P ^ cr) ^ 2 * F6 * Γ) * (σ₁ ^ (-e) * σ₂ ^ (-e)) := by sorry

alias «Formalism».«MainNotions».«BridgeLemma₂».«rows_num_pair» := P2M_Formalism_MainNotions_BridgeLemma__rows_num_pair_e1a5b5481773
