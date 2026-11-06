-- Prove2me | Theorems.Thm_QEC_Semantics_exists_finiteKrausFamily_of_choiMatrix_posSemidef
-- name    : QEC.Semantics.exists_finiteKrausFamily_of_choiMatrix_posSemidef
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:14:13.095213+00:00
-- url     : https://prove2.me/theorems/5a26eccd-0f22-454b-8780-c559620eafc0
-- title:
--   Semantics: exists finite Kraus Family of choi Matrix pos Semidef
-- statement:
--   A positive semidefinite project-local Choi matrix yields a finite Kraus family
--   whose induced operator-space map is the original map.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/ChoiKraus.lean#L180-L197
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/ChoiKraus.lean#L180-L197

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

theorem QEC.Semantics.exists_finiteKrausFamily_of_choiMatrix_posSemidef {n : Nat} {betaK : Type*}
    [Fintype betaK]
    (Φ : Operator H →ₗ[Complex] Operator K)
    (bH : OrthonormalBasis (Fin n) Complex H)
    (bK : OrthonormalBasis betaK Complex K)
    (hchoi : (choiMatrix Φ bH bK).PosSemidef) :
    ∃ (m : Nat), ∃ R : FiniteKrausFamily (Fin m) H K,
      R.inducedMap = Φ := by sorry
