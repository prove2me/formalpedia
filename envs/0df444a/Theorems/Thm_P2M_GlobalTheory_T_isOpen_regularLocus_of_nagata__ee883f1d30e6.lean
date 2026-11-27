-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_isOpen_regularLocus_of_nagata__ee883f1d30e6
-- name    : P2M_GlobalTheory_T_isOpen_regularLocus_of_nagata__ee883f1d30e6
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:07:29.401707+00:00
-- url     : https://prove2.me/theorems/752f2e5e-9a57-5a05-8fbb-1dfc7c46d2e5
-- title:
--   P2 M Global Theory T is Open regular Locus of nagata  ee883f1d30e6: P2 M Global Theory T is Open regular Locus of nagata  ee883f1d30e6
-- statement:
--   The P2 M Global Theory T is Open regular Locus of nagata  ee883f1d30e6 construction uses the P2 M Global Theory T is Open regular Locus of nagata  ee883f1d30e6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsOpenRegularLocusOfNagataStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsOpenRegularLocusOfNagataStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenRegularLocusOfNagata
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenRegularLocusOfNagataStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_isOpen_regularLocus_of_nagata__ee883f1d30e6 : ∀ (B : Type) [CommRing B] [IsNoetherianRing B], (∀ (p : Ideal B) [p.IsPrime], ∃ g, g ∉ p ∧ ∀ (q : Ideal B) [q.IsPrime], p ≤ q → g ∉ q → IsRegularLocalRing (Localization.AtPrime q ⧸ p.map (algebraMap B (Localization.AtPrime q)))) → IsOpen {Q : PrimeSpectrum B | IsRegularLocalRing (Localization.AtPrime Q.asIdeal)} := by sorry

alias «GlobalTheory».«T».«isOpen_regularLocus_of_nagata'» := P2M_GlobalTheory_T_isOpen_regularLocus_of_nagata__ee883f1d30e6
