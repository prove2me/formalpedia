-- Prove2me | Theorems.Thm_QEC_Locality_exists_qudit_erasureRecovery_of_subset
-- name    : QEC.Locality.exists_qudit_erasureRecovery_of_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:01:21.99853+00:00
-- url     : https://prove2.me/theorems/36c3c73e-a848-43f9-8eeb-37e12682f2af
-- title:
--   Locality: exists qudit erasure Recovery of subset
-- statement:
--   Erasing a larger finite qudit region with a concrete CPTP recovery implies
--   concrete recovery for every selected subset, by discarding the additionally
--   retained coordinates before applying the original recovery.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/CorrectableRegionClosure.lean#L766-L775
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/CorrectableRegionClosure.lean#L766-L775

import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
import Definitions.Def_QEC_Coding_Stabilizer_FixedGeneratorInteraction
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding
open PauliSymplectic
universe u v w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.exists_qudit_erasureRecovery_of_subset
    {q : ι → Nat} (S T : QuditSubsystem q) (hST : S.selected ⊆ T.selected)
    (C : QuantumCode (Qudit.QuditRegister q))
    (hRecovery : ∃ recovery : QuantumChannel T.complementSystem (Qudit.QuditRegister q),
      Correctable (Qudit.QuditRegister q) T.complementSystem C
        T.erasureChannelFromRegister recovery) :
    ∃ recovery : QuantumChannel S.complementSystem (Qudit.QuditRegister q),
      Correctable (Qudit.QuditRegister q) S.complementSystem C
        S.erasureChannelFromRegister recovery := by sorry
