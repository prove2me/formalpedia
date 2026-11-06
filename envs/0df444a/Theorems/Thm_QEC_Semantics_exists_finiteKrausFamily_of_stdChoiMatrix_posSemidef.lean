-- Prove2me | Theorems.Thm_QEC_Semantics_exists_finiteKrausFamily_of_stdChoiMatrix_posSemidef
-- name    : QEC.Semantics.exists_finiteKrausFamily_of_stdChoiMatrix_posSemidef
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:14:20.924319+00:00
-- url     : https://prove2.me/theorems/7d48936c-311e-41a2-8aaa-ba8c3d0c5877
-- title:
--   Semantics: exists finite Kraus Family of std Choi Matrix pos Semidef
-- statement:
--   Standard-basis wrapper for finite-dimensional systems.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/ChoiKraus.lean#L202-L208
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/ChoiKraus.lean#L202-L208

import Definitions.Def_QEC_Semantics_Channels_Choi
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]

theorem QEC.Semantics.exists_finiteKrausFamily_of_stdChoiMatrix_posSemidef
    (Φ : Operator H →ₗ[Complex] Operator K)
    (hchoi : (stdChoiMatrix Φ).PosSemidef) :
    ∃ (m : Nat), ∃ R : FiniteKrausFamily (Fin m) H K,
      R.inducedMap = Φ := by sorry
