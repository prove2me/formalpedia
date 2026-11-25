-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_LimitOfFinite_exists_limit_of_finite__77fbe7ded2da
-- name    : P2M_UpperTheory_Reformulated_B_LimitOfFinite_exists_limit_of_finite__77fbe7ded2da
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:43:42.886204+00:00
-- url     : https://prove2.me/theorems/6e34a311-1c55-51cf-806c-4d47cd5fe7cb
-- title:
--   P2 M Upper Theory Reformulated B Limit Of Finite exists limit of finite  77fbe7ded2da: P2 M Upper Theory Reformulated B Limit Of Finite exists limit of finite  77fbe7ded2da
-- statement:
--   The P2 M Upper Theory Reformulated B Limit Of Finite exists limit of finite  77fbe7ded2da construction uses the P2 M Upper Theory Reformulated B Limit Of Finite exists limit of finite  77fbe7ded2da property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/LimitOfFinite.lean#L62-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/LimitOfFinite.lean#L62-L172

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LimitOfFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem P2M_UpperTheory_Reformulated_B_LimitOfFinite_exists_limit_of_finite__77fbe7ded2da.{u_1, u_2} :
    ∀ {A : Type u_1} {M : Type u_2} [inst : CommRing A] [inst_1 : AddCommGroup M]
      [inst_2 :
        @_root_.Module A M (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
          (@AddCommGroup.toAddCommMonoid M inst_1)]
      [@Module.Finite A M (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
          (@AddCommGroup.toAddCommMonoid M inst_1) inst_2]
      (I : @Ideal A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))),
      @IsPrecomplete A inst I A (@Ring.toAddCommGroup A (@CommRing.toRing A inst))
          (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))) →
        ∀ (f : Nat → M),
          (∀ (m : Nat),
              @Membership.mem M
                (@Submodule A M (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
                  (@AddCommGroup.toAddCommMonoid M inst_1) inst_2)
                (@SetLike.instMembership
                  (@Submodule A M (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
                    (@AddCommGroup.toAddCommMonoid M inst_1) inst_2)
                  M
                  (@Submodule.setLike A M (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
                    (@AddCommGroup.toAddCommMonoid M inst_1) inst_2))
                (@HSMul.hSMul (@Ideal A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                  (@Submodule A M (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
                    (@AddCommGroup.toAddCommMonoid M inst_1) inst_2)
                  (@Submodule A M (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
                    (@AddCommGroup.toAddCommMonoid M inst_1) inst_2)
                  (@instHSMul (@Ideal A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                    (@Submodule A M (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
                      (@AddCommGroup.toAddCommMonoid M inst_1) inst_2)
                    (@Submodule.instSMul A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)) A
                      (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
                      (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))) M
                      (@AddCommGroup.toAddCommMonoid M inst_1) inst_2 inst_2
                      (@IsScalarTower.left A M
                        (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                        (@DistribMulAction.toMulAction A M
                          (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                          (@AddCommMonoid.toAddMonoid M (@AddCommGroup.toAddCommMonoid M inst_1))
                          (@Module.toDistribMulAction A M (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
                            (@AddCommGroup.toAddCommMonoid M inst_1) inst_2)))))
                  (@HPow.hPow (@Ideal A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))) Nat
                    (@Ideal A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                    (@instHPow (@Ideal A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))) Nat
                      (@Submodule.instPowNat A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)) A
                        (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
                        (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                        (@IsScalarTower.right A A (@CommRing.toCommSemiring A inst)
                          (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
                          (@Algebra.id A (@CommRing.toCommSemiring A inst)))))
                    I m)
                  (@Top.top
                    (@Submodule A M (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
                      (@AddCommGroup.toAddCommMonoid M inst_1) inst_2)
                    (@Submodule.instTop A M (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
                      (@AddCommGroup.toAddCommMonoid M inst_1) inst_2)))
                (@HSub.hSub M M M
                  (@instHSub M (@SubNegMonoid.toSub M (@AddGroup.toSubNegMonoid M (@AddCommGroup.toAddGroup M inst_1))))
                  (f m)
                  (f
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) →
            ∃ (L : M),
              ∀ (m : Nat),
                @Membership.mem M
                  (@Submodule A M (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
                    (@AddCommGroup.toAddCommMonoid M inst_1) inst_2)
                  (@SetLike.instMembership
                    (@Submodule A M (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
                      (@AddCommGroup.toAddCommMonoid M inst_1) inst_2)
                    M
                    (@Submodule.setLike A M (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
                      (@AddCommGroup.toAddCommMonoid M inst_1) inst_2))
                  (@HSMul.hSMul (@Ideal A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                    (@Submodule A M (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
                      (@AddCommGroup.toAddCommMonoid M inst_1) inst_2)
                    (@Submodule A M (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
                      (@AddCommGroup.toAddCommMonoid M inst_1) inst_2)
                    (@instHSMul (@Ideal A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                      (@Submodule A M (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
                        (@AddCommGroup.toAddCommMonoid M inst_1) inst_2)
                      (@Submodule.instSMul A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)) A
                        (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
                        (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))) M
                        (@AddCommGroup.toAddCommMonoid M inst_1) inst_2 inst_2
                        (@IsScalarTower.left A M
                          (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                          (@DistribMulAction.toMulAction A M
                            (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                            (@AddCommMonoid.toAddMonoid M (@AddCommGroup.toAddCommMonoid M inst_1))
                            (@Module.toDistribMulAction A M (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
                              (@AddCommGroup.toAddCommMonoid M inst_1) inst_2)))))
                    (@HPow.hPow (@Ideal A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))) Nat
                      (@Ideal A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                      (@instHPow (@Ideal A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))) Nat
                        (@Submodule.instPowNat A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)) A
                          (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
                          (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                          (@IsScalarTower.right A A (@CommRing.toCommSemiring A inst)
                            (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
                            (@Algebra.id A (@CommRing.toCommSemiring A inst)))))
                      I m)
                    (@Top.top
                      (@Submodule A M (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
                        (@AddCommGroup.toAddCommMonoid M inst_1) inst_2)
                      (@Submodule.instTop A M (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
                        (@AddCommGroup.toAddCommMonoid M inst_1) inst_2)))
                  (@HSub.hSub M M M
                    (@instHSub M (@SubNegMonoid.toSub M (@AddGroup.toSubNegMonoid M (@AddCommGroup.toAddGroup M inst_1))))
                    (f m) L) := by sorry

alias «UpperTheory».«Reformulated».«B».«LimitOfFinite».«exists_limit_of_finite».«» := P2M_UpperTheory_Reformulated_B_LimitOfFinite_exists_limit_of_finite__77fbe7ded2da
