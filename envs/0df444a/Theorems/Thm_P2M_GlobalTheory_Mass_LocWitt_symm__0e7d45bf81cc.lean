-- Prove2me | Theorems.Thm_P2M_GlobalTheory_Mass_LocWitt_symm__0e7d45bf81cc
-- name    : P2M_GlobalTheory_Mass_LocWitt_symm__0e7d45bf81cc
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:54:43.259859+00:00
-- url     : https://prove2.me/theorems/5fcb2547-f4b2-426c-b197-7f1fd3816861
-- title:
--   P2 M Global Theory Mass Loc Witt symm  0e7d45bf81cc: P2 M Global Theory Mass Loc Witt symm  0e7d45bf81cc
-- statement:
--   The P2 M Global Theory Mass Loc Witt symm  0e7d45bf81cc construction uses the P2 M Global Theory Mass Loc Witt symm  0e7d45bf81cc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemHcompl.lean#L25-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemHcompl.lean#L25-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemHcompl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.LocWitt
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

theorem P2M_GlobalTheory_Mass_LocWitt_symm__0e7d45bf81cc {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (x y : V) : star (h x y) = h y x := by sorry

alias «GlobalTheory».«Mass».«LocWitt».«symm'» := P2M_GlobalTheory_Mass_LocWitt_symm__0e7d45bf81cc
