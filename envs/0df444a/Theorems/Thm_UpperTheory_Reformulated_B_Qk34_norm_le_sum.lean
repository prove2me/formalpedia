-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_Qk34_norm_le_sum
-- name    : UpperTheory.Reformulated.B.Qk34.norm_le_sum
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:12:45.254798+00:00
-- url     : https://prove2.me/theorems/4adfa018-43da-4409-9c81-1416b1145ddf
-- title:
--   Qk34: norm le sum
-- statement:
--   The Qk34 construction uses the norm le sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/NormLeSum.lean#L7-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/NormLeSum.lean#L7-L29

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormLeSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.Qk34.norm_le_sum :
    ∀ (P Q : Nat) (X : UpperTheory.Reformulated.B.Qk34.MM P Q),
      @LE.le Real Real.instLE
        (@Norm.norm (UpperTheory.Reformulated.B.Qk34.MM P Q)
          (@NormedRing.toNorm (UpperTheory.Reformulated.B.Qk34.MM P Q)
            (@Matrix.linftyOpNormedRing (Sum (Fin P) (Fin Q)) Complex
              (@instFintypeSum (Fin P) (Fin Q) (Fin.fintype P) (Fin.fintype Q))
              (@CStarAlgebra.toNormedRing Complex (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
              fun (a b : Sum (Fin P) (Fin Q)) ↦
              @instDecidableEqSum (Fin P) (Fin Q) (instDecidableEqFin P) (instDecidableEqFin Q) a b))
          X)
        (∑ i : Sum (Fin P) (Fin Q), ∑ j : Sum (Fin P) (Fin Q), @Norm.norm Complex Complex.instNorm (X i j)) := by sorry
