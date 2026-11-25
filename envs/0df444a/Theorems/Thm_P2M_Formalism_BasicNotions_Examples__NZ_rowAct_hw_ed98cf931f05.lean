-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_rowAct_hw_ed98cf931f05
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_rowAct_hw_ed98cf931f05
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:53:43.081434+00:00
-- url     : https://prove2.me/theorems/0f91f31a-b0e3-46bc-8b68-3b196c4f33e8
-- title:
--   P2 M Formalism Basic Notions Examples  NZ row Act hw ed98cf931f05: P2 M Formalism Basic Notions Examples  NZ row Act hw ed98cf931f05
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ row Act hw ed98cf931f05 construction uses the P2 M Formalism Basic Notions Examples  NZ row Act hw ed98cf931f05 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZLevB.lean#L49-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZLevB.lean#L49-L54

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

theorem P2M_Formalism_BasicNotions_Examples__NZ_rowAct_hw_ed98cf931f05 (hn : n ≤ r) (ν : Fin n → ℕ) (h : Matrix (Fin r) (Fin r) R) (hl : ∀ i j, i < j → h i j = 0) :
    rowAct R h (hw R hn ν) = hwScal R hn ν h • hw R hn ν := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«rowAct_hw» := P2M_Formalism_BasicNotions_Examples__NZ_rowAct_hw_ed98cf931f05
