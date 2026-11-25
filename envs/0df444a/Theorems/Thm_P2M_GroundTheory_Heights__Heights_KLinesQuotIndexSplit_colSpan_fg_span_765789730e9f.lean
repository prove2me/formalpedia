-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesQuotIndexSplit_colSpan_fg_span_765789730e9f
-- name    : P2M_GroundTheory_Heights__Heights_KLinesQuotIndexSplit_colSpan_fg_span_765789730e9f
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:26:34.968391+00:00
-- url     : https://prove2.me/theorems/84e89a46-d2d1-408c-971f-4bc468ce9afd
-- title:
--   P2 M Ground Theory Heights  Heights KLines Quot Index Split col Span fg span 765789730e9f: P2 M Ground Theory Heights  Heights KLines Quot Index Split col Span fg span 765789730e9f
-- statement:
--   The P2 M Ground Theory Heights  Heights KLines Quot Index Split col Span fg span 765789730e9f construction uses the P2 M Ground Theory Heights  Heights KLines Quot Index Split col Span fg span 765789730e9f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesQuotIndexSplit.lean#L13-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesQuotIndexSplit.lean#L13-L31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesQuotIndexSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.KLinesQuotIndexSplit

theorem P2M_GroundTheory_Heights__Heights_KLinesQuotIndexSplit_colSpan_fg_span_765789730e9f (K : Type) [Field K] [NumberField K] (k : ℕ)
    (V : Matrix (Fin k) (Fin k) K) (hV : V.det ≠ 0) :
    ((Submodule.span (𝓞 K) (Set.range fun j => V *ᵥ (Pi.single j 1 : Fin k → K))).restrictScalars
        ℤ).FG ∧
      Submodule.span K ((Submodule.span (𝓞 K)
          (Set.range fun j => V *ᵥ (Pi.single j 1 : Fin k → K)) : Submodule (𝓞 K) (Fin k → K)) :
            Set (Fin k → K)) = ⊤ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KLinesQuotIndexSplit».«colSpan_fg_span» := P2M_GroundTheory_Heights__Heights_KLinesQuotIndexSplit_colSpan_fg_span_765789730e9f
