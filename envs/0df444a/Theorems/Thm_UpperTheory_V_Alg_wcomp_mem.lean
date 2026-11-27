-- Prove2me | Theorems.Thm_UpperTheory_V_Alg_wcomp_mem
-- name    : UpperTheory.V.Alg.wcomp_mem
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:40:15.558441+00:00
-- url     : https://prove2.me/theorems/b5a31ff0-1171-5a5b-a4f3-9edc513e09a9
-- title:
--   Alg: wcomp mem
-- statement:
--   The Alg construction uses the wcomp mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/CommutativeAlgebra/ResMapBijective.lean#L102-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/CommutativeAlgebra/ResMapBijective.lean#L102-L103

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_CommutativeAlgebra_ResMapBijective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsLocalRing MvPowerSeries
open UpperTheory UpperTheory.V UpperTheory.V.Alg
attribute [instance] IsCO.complete IsCO.isLocalHom
variable (O : Type) [CommRing O] {σ X : Type} [AddCommGroup X] (wt : σ → X)

theorem UpperTheory.V.Alg.wcomp_mem (j : X) (f : MvPowerSeries σ O) : wcomp O wt j f ∈ wtPart O wt j := by sorry
