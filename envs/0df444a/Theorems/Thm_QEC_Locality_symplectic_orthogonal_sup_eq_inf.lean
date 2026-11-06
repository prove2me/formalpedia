-- Prove2me | Theorems.Thm_QEC_Locality_symplectic_orthogonal_sup_eq_inf
-- name    : QEC.Locality.symplectic_orthogonal_sup_eq_inf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:32:33.501179+00:00
-- url     : https://prove2.me/theorems/fd24bbff-8a49-442e-bbf5-06272873c359
-- title:
--   Locality: symplectic orthogonal sup eq inf
-- statement:
--   The Locality construction uses the symplectic orthogonal sup eq inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/CorrectableRegionClosure.lean#L198-L212
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/CorrectableRegionClosure.lean#L198-L212

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
omit [DecidableEq ι]

theorem QEC.Locality.symplectic_orthogonal_sup_eq_inf
    (U V : Submodule (ZMod 2) (SymplecticVector (ZMod 2) ι)) :
    FiniteSymplectic.form.orthogonal (U ⊔ V) =
      FiniteSymplectic.form.orthogonal U ⊓ FiniteSymplectic.form.orthogonal V := by sorry
