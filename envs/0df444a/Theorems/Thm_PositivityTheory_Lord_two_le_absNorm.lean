-- Prove2me | Theorems.Thm_PositivityTheory_Lord_two_le_absNorm
-- name    : PositivityTheory.Lord.two_le_absNorm
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:50:25.0801+00:00
-- url     : https://prove2.me/theorems/d46e1b3f-7143-401c-b249-9c7ad5c275e2
-- title:
--   Lord: two le abs Norm
-- statement:
--   The Lord construction uses the two le abs Norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ZetaEulerProducts/FactorDifferentiable.lean#L73-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ZetaEulerProducts/FactorDifferentiable.lean#L73-L81

import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ZetaEulerProducts_MeromorphicAtProd
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ZetaEulerProducts_FactorDifferentiable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Complex NumberField IsDedekindDomain
open PositivityTheory PositivityTheory.Lord

theorem PositivityTheory.Lord.two_le_absNorm (K : Type) [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) :
    2 ≤ Ideal.absNorm P.asIdeal := by sorry
