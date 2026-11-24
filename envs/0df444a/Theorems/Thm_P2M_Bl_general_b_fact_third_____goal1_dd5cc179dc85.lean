-- Prove2me | Theorems.Thm_P2M_Bl_general_b_fact_third_____goal1_dd5cc179dc85
-- name    : P2M_Bl_general_b_fact_third_____goal1_dd5cc179dc85
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:35:39.440791+00:00
-- url     : https://prove2.me/theorems/119cf531-8f5e-4ad7-8a39-55c0a8d91ae3
-- title:
--   P2 M Bl general b fact third     goal1 dd5cc179dc85: P2 M Bl general b fact third     goal1 dd5cc179dc85
-- statement:
--   The P2 M Bl general b fact third     goal1 dd5cc179dc85 construction uses the P2 M Bl general b fact third     goal1 dd5cc179dc85 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactThirdRest/Imports.lean#L28-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactThirdRest/Imports.lean#L28-L59

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_SArith
import Definitions.Def_Formalism_LocalRingCardinality_Params
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_LocalRingCardinality_DataCoeff
import Definitions.Def_Formalism_LocalRingCardinality_DataArith
import Definitions.Def_Formalism_LocalRingCardinality_DataKernels
import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_DataS
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataG
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_FrobeniusOrbits_DiscrMaximalRealCyclotomic
import Definitions.Def_Formalism_FrobeniusOrbits_HostOrbitsPlaces
import Definitions.Def_Formalism_FrobeniusOrbits_HostDiffSupport
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_HostOrbitCountSg
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ConjEMemHostFIff
import Definitions.Def_Formalism_CoboundaryTransfers_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_RealCyclotomicSubfield
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_FinalGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_Galois
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_ConjEqInvOfPowEqOne
import Definitions.Def_Lemmata_GeneralBFactThirdRest_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_third''''

theorem P2M_Bl_general_b_fact_third_____goal1_dd5cc179dc85 :
  ∀ {E : Type} [inst : Field.{0} E] [inst_1 : NumberField.{0} E] [inst_2 : StarRing.{0} E] (S : Formalism.BasicNotions.HSpace E)
  (Λ : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} E) S.V),
  Submodule.IsLattice.{0, 0, 0} E Λ →
    ∀ (x : S.V),
      Exists.{1} fun (a : NumberField.RingOfIntegers.{0} E) ↦
        And (Ne.{1} a 0) (Membership.mem.{0, 0} Λ (HSMul.hSMul.{0, 0, 0} a x)) := by sorry

alias «Bl».«general_b_fact_third''''».«goal1» := P2M_Bl_general_b_fact_third_____goal1_dd5cc179dc85
