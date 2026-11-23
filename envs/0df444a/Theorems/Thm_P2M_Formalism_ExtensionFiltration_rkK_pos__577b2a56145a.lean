-- Prove2me | Theorems.Thm_P2M_Formalism_ExtensionFiltration_rkK_pos__577b2a56145a
-- name    : P2M_Formalism_ExtensionFiltration_rkK_pos__577b2a56145a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:03:19.660158+00:00
-- url     : https://prove2.me/theorems/19cb107e-bdf5-42cc-ae15-19eabaf1de65
-- title:
--   P2 M Formalism Extension Filtration rk K pos  577b2a56145a: P2 M Formalism Extension Filtration rk K pos  577b2a56145a
-- statement:
--   The P2 M Formalism Extension Filtration rk K pos  577b2a56145a construction uses the P2 M Formalism Extension Filtration rk K pos  577b2a56145a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MeanHeightDescent/AverageDegreeBounds/TwistLower.lean#L103-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MeanHeightDescent/AverageDegreeBounds/TwistLower.lean#L103-L113

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_MuMaxMinkowski
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_DescentSlope
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ShiftInvariance
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_TwistLower
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.ExtensionFiltration
open Formalism.HN
open scoped Pointwise
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
  [DecidableEq ι]
omit [StarRing K] [IsTotallyComplex K]

theorem P2M_Formalism_ExtensionFiltration_rkK_pos__577b2a56145a (M : Submodule (𝓞 K) V) (hM0 : M ≠ ⊥) [FiniteDimensional K V] : 0 < rkK (K := K) M := by sorry

alias «Formalism».«ExtensionFiltration».«rkK_pos'» := P2M_Formalism_ExtensionFiltration_rkK_pos__577b2a56145a
