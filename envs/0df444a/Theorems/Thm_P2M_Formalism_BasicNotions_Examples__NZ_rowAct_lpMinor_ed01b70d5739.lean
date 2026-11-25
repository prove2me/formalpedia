-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_rowAct_lpMinor_ed01b70d5739
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_rowAct_lpMinor_ed01b70d5739
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:53:53.43465+00:00
-- url     : https://prove2.me/theorems/a2eb3605-ae20-41dd-be52-2827974fb5fb
-- title:
--   P2 M Formalism Basic Notions Examples  NZ row Act lp Minor ed01b70d5739: P2 M Formalism Basic Notions Examples  NZ row Act lp Minor ed01b70d5739
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ row Act lp Minor ed01b70d5739 construction uses the P2 M Formalism Basic Notions Examples  NZ row Act lp Minor ed01b70d5739 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZLevB.lean#L16-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZLevB.lean#L16-L44

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_SwRowGenMonomial
import Definitions.Def_Lemmata_GeneralBFactRightBisForm_Imports
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZLevB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ
open Formalism.GradedWeylDivisibility
variable (R : Type) [CommRing R] {r n : ℕ}

theorem P2M_Formalism_BasicNotions_Examples__NZ_rowAct_lpMinor_ed01b70d5739 (h : Matrix (Fin r) (Fin r) R) (hl : ∀ i j, i < j → h i j = 0) (s : ℕ) (hr : s ≤ r) (hn : s ≤ n) :
    rowAct R h (lpMinor R (n := n) s hr hn) =
      C (∏ a : Fin s, h (Fin.castLE hr a) (Fin.castLE hr a)) * lpMinor R s hr hn := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«rowAct_lpMinor» := P2M_Formalism_BasicNotions_Examples__NZ_rowAct_lpMinor_ed01b70d5739
