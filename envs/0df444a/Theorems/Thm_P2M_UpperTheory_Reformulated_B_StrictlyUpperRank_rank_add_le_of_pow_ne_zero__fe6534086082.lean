-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_StrictlyUpperRank_rank_add_le_of_pow_ne_zero__fe6534086082
-- name    : P2M_UpperTheory_Reformulated_B_StrictlyUpperRank_rank_add_le_of_pow_ne_zero__fe6534086082
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:44:02.721589+00:00
-- url     : https://prove2.me/theorems/394fb285-fc0d-5fd2-a9f0-d81a86b69d27
-- title:
--   P2 M Upper Theory Reformulated B Strictly Upper Rank rank add le of pow ne zero  fe6534086082: P2 M Upper Theory Reformulated B Strictly Upper Rank rank add le of pow ne zero  fe6534086082
-- statement:
--   The P2 M Upper Theory Reformulated B Strictly Upper Rank rank add le of pow ne zero  fe6534086082 construction uses the P2 M Upper Theory Reformulated B Strictly Upper Rank rank add le of pow ne zero  fe6534086082 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/StrictlyUpperRank.lean#L36-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/StrictlyUpperRank.lean#L36-L91

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_StrictlyUpperRank
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem P2M_UpperTheory_Reformulated_B_StrictlyUpperRank_rank_add_le_of_pow_ne_zero__fe6534086082.{u_1, u_2} :
    ∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {n : Type u_2} [inst_1 : Fintype n] [inst_2 : LinearOrder n] {X : Matrix n n 𝕜},
      @UpperTheory.Reformulated.B.StrictlyUpperRank.IsStrictUpper 𝕜 inst n inst_2 X →
        ∀ (k : Nat) (i j : n),
          @Ne 𝕜
              (@HPow.hPow (Matrix n n 𝕜) Nat (Matrix n n 𝕜)
                (@instHPow (Matrix n n 𝕜) Nat
                  (@NPow.toPow (Matrix n n 𝕜)
                    (@Monoid.toNPow (Matrix n n 𝕜)
                      (@Semiring.toMonoid (Matrix n n 𝕜)
                        (@Matrix.semiring n 𝕜
                          (@DivisionSemiring.toSemiring 𝕜
                            (@Semifield.toDivisionSemiring 𝕜
                              (@Field.toSemifield 𝕜
                                (@NormedField.toField 𝕜
                                  (@DenselyNormedField.toNormedField 𝕜 (@RCLike.toDenselyNormedField 𝕜 inst))))))
                          inst_1 fun (a b : n) ↦ @LinearOrder.toDecidableEq n inst_2 a b)))))
                X k i j)
              (@OfNat.ofNat 𝕜 (nat_lit 0)
                (@Zero.toOfNat0 𝕜
                  (@MulZeroClass.toZero 𝕜
                    (@instMulZeroClassOfSemiring 𝕜
                      (@DivisionSemiring.toSemiring 𝕜
                        (@Semifield.toDivisionSemiring 𝕜
                          (@Field.toSemifield 𝕜
                            (@NormedField.toField 𝕜
                              (@DenselyNormedField.toNormedField 𝕜 (@RCLike.toDenselyNormedField 𝕜 inst)))))))))) →
            @LE.le Nat instLENat
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@UpperTheory.Reformulated.B.StrictlyUpperRank.rankBelow n inst_1 inst_2 i) k)
              (@UpperTheory.Reformulated.B.StrictlyUpperRank.rankBelow n inst_1 inst_2 j) := by sorry

alias «UpperTheory».«Reformulated».«B».«StrictlyUpperRank».«rank_add_le_of_pow_ne_zero».«» := P2M_UpperTheory_Reformulated_B_StrictlyUpperRank_rank_add_le_of_pow_ne_zero__fe6534086082
