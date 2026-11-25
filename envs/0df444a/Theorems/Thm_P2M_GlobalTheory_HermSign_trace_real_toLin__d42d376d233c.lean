-- Prove2me | Theorems.Thm_P2M_GlobalTheory_HermSign_trace_real_toLin__d42d376d233c
-- name    : P2M_GlobalTheory_HermSign_trace_real_toLin__d42d376d233c
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:06:07.260733+00:00
-- url     : https://prove2.me/theorems/305cda73-f206-42ec-9346-ade15e04900e
-- title:
--   P2 M Global Theory Herm Sign trace real to Lin  d42d376d233c: P2 M Global Theory Herm Sign trace real to Lin  d42d376d233c
-- statement:
--   The P2 M Global Theory Herm Sign trace real to Lin  d42d376d233c construction uses the P2 M Global Theory Herm Sign trace real to Lin  d42d376d233c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/SignatureHermitianModelOfDatum.lean#L163-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/SignatureHermitianModelOfDatum.lean#L163-L168

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_MemIffConjugateNotMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_SignatureHermitianModelOfDatum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors TensorProduct ComplexConjugate ComplexOrder MatrixOrder
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HermSign

theorem P2M_GlobalTheory_HermSign_trace_real_toLin__d42d376d233c {r : ℕ} (N : Matrix (Fin r) (Fin r) ℂ) :
    LinearMap.trace ℝ _ ((toLin' N).restrictScalars ℝ) = 2 * N.trace.re := by sorry

alias «GlobalTheory».«HermSign».«trace_real_toLin'» := P2M_GlobalTheory_HermSign_trace_real_toLin__d42d376d233c
