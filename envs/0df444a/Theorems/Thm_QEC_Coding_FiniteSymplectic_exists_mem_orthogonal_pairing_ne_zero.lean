-- Prove2me | Theorems.Thm_QEC_Coding_FiniteSymplectic_exists_mem_orthogonal_pairing_ne_zero
-- name    : QEC.Coding.FiniteSymplectic.exists_mem_orthogonal_pairing_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:48:43.782253+00:00
-- url     : https://prove2.me/theorems/5b770139-99cd-4477-897c-f78524e4987e
-- title:
--   Finite Symplectic: exists mem orthogonal pairing ne zero
-- statement:
--   Outside a subspace, some vector in its symplectic orthogonal has nonzero
--   pairing with the given vector. This is the finite-dimensional
--   double-orthogonal separation step used for logical Pauli partners.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Symplectic.lean#L157-L174
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Symplectic.lean#L157-L174

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Definitions.Def_QEC_Coding_Stabilizer_Symplectic
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
universe u v
open QEC.Coding.FiniteSymplectic
variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]

theorem QEC.Coding.FiniteSymplectic.exists_mem_orthogonal_pairing_ne_zero
    (S : Submodule F (SymplecticVector F ι))
    {e : SymplecticVector F ι}
    (_heOrthogonal : e ∈ (form (F := F) (ι := ι)).orthogonal S)
    (he : e ∉ S) :
    ∃ f, f ∈ (form (F := F) (ι := ι)).orthogonal S ∧ form e f ≠ 0 := by sorry
