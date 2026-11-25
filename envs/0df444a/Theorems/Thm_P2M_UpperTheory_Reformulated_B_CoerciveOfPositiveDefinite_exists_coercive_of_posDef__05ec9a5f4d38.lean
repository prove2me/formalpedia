-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_CoerciveOfPositiveDefinite_exists_coercive_of_posDef__05ec9a5f4d38
-- name    : P2M_UpperTheory_Reformulated_B_CoerciveOfPositiveDefinite_exists_coercive_of_posDef__05ec9a5f4d38
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:20:45.996516+00:00
-- url     : https://prove2.me/theorems/3c09e76e-778c-5c41-b18b-ec6f4cce9930
-- title:
--   P2 M Upper Theory Reformulated B Coercive Of Positive Definite exists coercive of pos Def  05ec9a5f4d38: P2 M Upper Theory Reformulated B Coercive Of Positive Definite exists coercive of pos Def  05ec
-- statement:
--   The P2 M Upper Theory Reformulated B Coercive Of Positive Definite exists coercive of pos Def  05ec9a5f4d38 construction uses the P2 M Upper Theory Reformulated B Coercive Of Positive Definite exists coercive of pos Def  05ec9a5f4d38 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/CoerciveOfPositiveDefinite.lean#L3-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/CoerciveOfPositiveDefinite.lean#L3-L66

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CoerciveOfPositiveDefinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem P2M_UpperTheory_Reformulated_B_CoerciveOfPositiveDefinite_exists_coercive_of_posDef__05ec9a5f4d38.{u_1} :
    ∀ {ι : Type u_1} [inst : Fintype ι] {P : Matrix ι ι Complex},
      @Matrix.PosDef ι Complex Complex.instRing Complex.partialOrder Complex.instStarRing P →
        ∃ (c : Real),
          And (@LT.lt Real Real.instLT (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) c)
            (∀ (z : ι → Complex) (j : ι),
              @LE.le Real Real.instLE
                (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) c
                  (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))
                    (@Norm.norm Complex Complex.instNorm (z j)) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (@dotProduct ι Complex inst Complex.instMul Complex.instAddCommMonoid
                    (@Star.star (ι → Complex)
                      (@Pi.instStarForall ι (fun (a : ι) ↦ Complex) fun (i : ι) ↦
                        @InvolutiveStar.toStar Complex
                          (@StarAddMonoid.toInvolutiveStar Complex
                            (@AddCommMonoid.toAddMonoid Complex
                              (@NonUnitalNonAssocSemiring.toAddCommMonoid Complex
                                (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring Complex
                                  (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Complex
                                    (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Complex
                                      Complex.instNonUnitalCommRing)))))
                            (@StarRing.toStarAddMonoid Complex
                              (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring Complex
                                (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Complex
                                  (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Complex Complex.instNonUnitalCommRing)))
                              Complex.instStarRing)))
                      z)
                    (@Matrix.mulVec ι ι Complex
                      (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring Complex
                        (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Complex
                          (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Complex Complex.instNonUnitalCommRing)))
                      inst P z)).re) := by sorry

alias «UpperTheory».«Reformulated».«B».«CoerciveOfPositiveDefinite».«exists_coercive_of_posDef».«» := P2M_UpperTheory_Reformulated_B_CoerciveOfPositiveDefinite_exists_coercive_of_posDef__05ec9a5f4d38
