-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_mem_coneSub_38e4656e6965
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_mem_coneSub_38e4656e6965
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:33:12.135908+00:00
-- url     : https://prove2.me/theorems/9291faf5-ee44-5e76-8610-0dc0e5596c48
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub mem cone Sub 38e4656e6965: P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub mem cone Sub 38e4656e6965
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub mem cone Sub 38e4656e6965 construction uses the P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub mem cone Sub 38e4656e6965 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeTailCone.lean#L149-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeTailCone.lean#L149-L150

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTildeTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTailCone
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} (M : FinGradedSub (S := S) (x := x) Ω)

theorem P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_mem_coneSub_38e4656e6965 {w : ConeLaurent S x} : w ∈ M.coneSub ↔ ∀ c, coeffAt S x c w ∈ M.piece c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«FinGradedSub».«mem_coneSub» := P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_mem_coneSub_38e4656e6965
