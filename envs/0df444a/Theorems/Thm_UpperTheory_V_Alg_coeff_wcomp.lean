-- Prove2me | Theorems.Thm_UpperTheory_V_Alg_coeff_wcomp
-- name    : UpperTheory.V.Alg.coeff_wcomp
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:13:14.311775+00:00
-- url     : https://prove2.me/theorems/a161b4c9-e307-453a-9eaf-d85b209b64c6
-- title:
--   Alg: coeff wcomp
-- statement:
--   The Alg construction uses the coeff wcomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/CommutativeAlgebra/ResMapBijective.lean#L99-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/CommutativeAlgebra/ResMapBijective.lean#L99-L100

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
open Classical

theorem UpperTheory.V.Alg.coeff_wcomp (j : X) (f : MvPowerSeries σ O) (n : σ →₀ ℕ) :
    coeff n (wcomp O wt j f) = if Finsupp.weight wt n = j then coeff n f else 0 := by sorry
