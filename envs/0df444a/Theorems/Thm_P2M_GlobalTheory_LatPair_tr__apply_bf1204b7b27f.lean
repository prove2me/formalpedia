-- Prove2me | Theorems.Thm_P2M_GlobalTheory_LatPair_tr__apply_bf1204b7b27f
-- name    : P2M_GlobalTheory_LatPair_tr__apply_bf1204b7b27f
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:26.1888+00:00
-- url     : https://prove2.me/theorems/241509c1-bc37-473a-9639-e2647ca62281
-- title:
--   P2 M Global Theory Lat Pair tr  apply bf1204b7b27f: P2 M Global Theory Lat Pair tr  apply bf1204b7b27f
-- statement:
--   The P2 M Global Theory Lat Pair tr  apply bf1204b7b27f construction uses the P2 M Global Theory Lat Pair tr  apply bf1204b7b27f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/HasConductorMulShift.lean#L109-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/HasConductorMulShift.lean#L109-L109

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsGlOfEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.LatPair
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type*}
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
variable (q : Unif k) (χ : AddChar 𝓀[k] ℂ) (φ : Form k n M)

theorem P2M_GlobalTheory_LatPair_tr__apply_bf1204b7b27f (P : Pair k n) : tr' φ P = ∑ Q ∈ withKer P.ker, φ Q := by sorry

alias «GlobalTheory».«LatPair».«tr'_apply» := P2M_GlobalTheory_LatPair_tr__apply_bf1204b7b27f
