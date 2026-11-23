-- Prove2me | Theorems.Thm_QH_twist_prim
-- name    : QH.twist_prim
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:03:33.797232+00:00
-- url     : https://prove2.me/theorems/039fb382-d374-4eeb-b003-a38bae2cf765
-- title:
--   QH: twist prim
-- statement:
--   The QH construction uses the twist prim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/MeanSquareBounds/TwistPrim.lean#L9-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/MeanSquareBounds/TwistPrim.lean#L9-L18

import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_PrimeSetTwoBounds
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_TwistIsPrimitiveCharacter
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_WeightedVonMangoldtSumIdentity
import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_TwistPrim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
open QH

theorem QH.twist_prim :
    ∀ (f q : ℕ) [NeZero f] (ξ : DirichletCharacter ℂ f), ξ.IsPrimitive → q.Prime → q ≠ 2 → ¬ q ∣ f →
      ∃ ψ : DirichletCharacter ℂ (f * q), ψ.IsPrimitive ∧ ψ ≠ 1 ∧ ∀ n : ℕ, ψ (n : ZMod (f * q)) = ξ (n : ZMod f) * J q n := by sorry
