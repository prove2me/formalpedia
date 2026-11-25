-- Prove2me | Theorems.Thm_PI_Dv_TIW_span_map_matV
-- name    : PI.Dv.TIW.span_map_matV
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:19:56.214162+00:00
-- url     : https://prove2.me/theorems/fe82d8e6-11a6-42a3-9eae-018a4b3d9496
-- title:
--   TIW: span map mat V
-- statement:
--   The TIW construction uses the span map mat V property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/MatVTransvection.lean#L62-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/MatVTransvection.lean#L62-L67

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_IdxSmulSubMap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_MatVTransvection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.TIW
open Formalism.BasicNotions NumberField IsDedekindDomain PI.Dv
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem PI.Dv.TIW.span_map_matV {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n K) (hA : A.det ≠ 0)
    (L : Submodule (𝓞 K) (n → V)) (S : Submodule K V)
    (hL : Submodule.span K (L : Set (n → V)) = Submodule.pi Set.univ fun _ : n => S) :
    Submodule.span K ((L.map ((matV A).restrictScalars (𝓞 K)) : Submodule (𝓞 K) (n → V)) : Set (n → V)) =
      Submodule.pi Set.univ fun _ : n => S := by sorry
