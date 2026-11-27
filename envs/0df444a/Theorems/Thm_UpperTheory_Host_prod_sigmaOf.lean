-- Prove2me | Theorems.Thm_UpperTheory_Host_prod_sigmaOf
-- name    : UpperTheory.Host.prod_sigmaOf
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-27T05:37:06.425892+00:00
-- url     : https://prove2.me/theorems/204ac00f-44cf-54bc-95ab-076ab27a0516
-- title:
--   Host: prod sigma Of
-- statement:
--   The Host construction uses the prod sigma Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimeDiscriminants/MuParallel.lean#L33-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimeDiscriminants/MuParallel.lean#L33-L37

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ProdNegOneZpow
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_MuParallel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open UpperTheory UpperTheory.Host
open Formalism.BasicNotions NumberField
variable {R : Ranks} (H : Host R)

theorem UpperTheory.Host.prod_sigmaOf [Fintype R.Psi] (x : H.E) :
    ∏ g : R.Psi, H.sigmaOf (g : R.GG) x = algebraMap H.K H.E (Algebra.norm H.K x) := by sorry
