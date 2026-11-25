-- Prove2me | Theorems.Thm_P2M_PI_VolStabW_TopoMuInv_smul_neg__7eb46811fd83
-- name    : P2M_PI_VolStabW_TopoMuInv_smul_neg__7eb46811fd83
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:04:16.690804+00:00
-- url     : https://prove2.me/theorems/1f470bcf-e656-4461-a1fc-41ebc36f68c4
-- title:
--   P2 M PI Vol Stab W Topo Mu Inv smul neg  7eb46811fd83: P2 M PI Vol Stab W Topo Mu Inv smul neg  7eb46811fd83
-- statement:
--   The P2 M PI Vol Stab W Topo Mu Inv smul neg  7eb46811fd83 construction uses the P2 M PI Vol Stab W Topo Mu Inv smul neg  7eb46811fd83 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/TopoMuInv.lean#L46-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/TopoMuInv.lean#L46-L49

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoFibInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoMuInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.TopoMuInv
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Matrix NumberField IsDedekindDomain
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [SecondCountableTopology R] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem P2M_PI_VolStabW_TopoMuInv_smul_neg__7eb46811fd83 (h : HA R σ J) {n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) :
    h • (-X) = -(h • X) := by sorry

alias «PI».«VolStabW».«TopoMuInv».«smul_neg'» := P2M_PI_VolStabW_TopoMuInv_smul_neg__7eb46811fd83
