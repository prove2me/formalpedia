-- Prove2me | Theorems.Thm_P2M_GlobalTheory_coh_equiv__toH_77444994ce05
-- name    : P2M_GlobalTheory_coh_equiv__toH_77444994ce05
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:07:26.18337+00:00
-- url     : https://prove2.me/theorems/69586f4b-cfe0-487c-8942-2600bf4a9de5
-- title:
--   P2 M Global Theory coh equiv  to H 77444994ce05: P2 M Global Theory coh equiv  to H 77444994ce05
-- statement:
--   The P2 M Global Theory coh equiv  to H 77444994ce05 construction uses the P2 M Global Theory coh equiv  to H 77444994ce05 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/HdimEqZeroOfSubsingleton.lean#L493-L495
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/HdimEqZeroOfSubsingleton.lean#L493-L495

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ToAbSheafPreservesFiniteLimits
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
universe t v u
noncomputable section
open GlobalTheory
variable {X : Scheme.{u}}
open GlobalTheory.coh

theorem P2M_GlobalTheory_coh_equiv__toH_77444994ce05 (F : X.Modules) (x : coh F 0) :
    Sheaf.H.equiv₀ ((toAbSheaf X).obj F) isTerminalTop (toH F 0 x) = zeroEquiv F x := by sorry

alias «GlobalTheory».«coh».«equiv₀_toH» := P2M_GlobalTheory_coh_equiv__toH_77444994ce05
