-- Prove2me | Theorems.Thm_QEC_Semantics_choiMatrix_finiteKrausFamilyOfChoiVectors_inducedMap
-- name    : QEC.Semantics.choiMatrix_finiteKrausFamilyOfChoiVectors_inducedMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:14:10.633505+00:00
-- url     : https://prove2.me/theorems/6e574177-2463-4b41-a96d-b02e17f178ed
-- title:
--   Semantics: choi Matrix finite Kraus Family Of Choi Vectors induced Map
-- statement:
--   The Choi matrix of the induced map from Choi-coordinate Kraus branches is the
--   sum of the rank-one outer products of those coordinate vectors.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/ChoiKraus.lean#L139-L174
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/ChoiKraus.lean#L139-L174

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

theorem QEC.Semantics.choiMatrix_finiteKrausFamilyOfChoiVectors_inducedMap {m n : Nat} {betaK : Type*}
    [Fintype betaK]
    (bH : OrthonormalBasis (Fin n) Complex H)
    (bK : OrthonormalBasis betaK Complex K)
    (v : Fin m → (Fin n × betaK → Complex)) :
    choiMatrix ((finiteKrausFamilyOfChoiVectors bH bK v).inducedMap) bH bK =
      ∑ a : Fin m, Matrix.vecMulVec (v a) (star (v a)) := by sorry
