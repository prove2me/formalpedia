-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_IntegralPolynomialOverPadicAlgCl_intMv_X__37500283e46a
-- name    : P2M_UpperTheory_Reformulated_B_IntegralPolynomialOverPadicAlgCl_intMv_X__37500283e46a
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:21:28.81606+00:00
-- url     : https://prove2.me/theorems/8475d8cb-6ff0-5c1d-9d72-2ee64f7edc0a
-- title:
--   P2 M Upper Theory Reformulated B Integral Polynomial Over Padic Alg Cl int Mv X  37500283e46a: P2 M Upper Theory Reformulated B Integral Polynomial Over Padic Alg Cl int Mv X  37500283e46a
-- statement:
--   The P2 M Upper Theory Reformulated B Integral Polynomial Over Padic Alg Cl int Mv X  37500283e46a construction uses the P2 M Upper Theory Reformulated B Integral Polynomial Over Padic Alg Cl int Mv X  37500283e46a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/IntegralPolynomialFifth.lean#L315-L347
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/IntegralPolynomialFifth.lean#L315-L347

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IntegralPolynomialFifth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem P2M_UpperTheory_Reformulated_B_IntegralPolynomialOverPadicAlgCl_intMv_X__37500283e46a.{u_1} :
    ∀ {p : Nat} [inst : Fact (Nat.Prime p)] {σ : Type u_1} (i : σ),
      @UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.IntegralMv σ p inst
        (@MvPowerSeries.X σ (@PadicComplex p inst)
          (@DivisionSemiring.toSemiring (@PadicComplex p inst)
            (@Semifield.toDivisionSemiring (@PadicComplex p inst)
              (@Field.toSemifield (@PadicComplex p inst)
                (@UniformSpace.Completion.instField (@PadicAlgCl p inst)
                  (@AlgebraicClosure.instField (@Padic p inst) (@instFieldPadic p inst))
                  (@Valued.toUniformSpace (@PadicAlgCl p inst)
                    (@DivisionRing.toRing (@PadicAlgCl p inst)
                      (@Field.toDivisionRing (@PadicAlgCl p inst)
                        (@AlgebraicClosure.instField (@Padic p inst) (@instFieldPadic p inst))))
                    NNReal NNReal.instLinearOrderedCommGroupWithZero (@PadicAlgCl.valued p inst))
                  (@Valued.isTopologicalDivisionRing (@PadicAlgCl p inst)
                    (@Field.toDivisionRing (@PadicAlgCl p inst)
                      (@AlgebraicClosure.instField (@Padic p inst) (@instFieldPadic p inst)))
                    NNReal NNReal.instLinearOrderedCommGroupWithZero (@PadicAlgCl.valued p inst))
                  (@NormedField.instCompletableTopField (@PadicAlgCl p inst) (@PadicAlgCl.normedField p inst))
                  (@Valued.toIsUniformAddGroup (@PadicAlgCl p inst)
                    (@DivisionRing.toRing (@PadicAlgCl p inst)
                      (@Field.toDivisionRing (@PadicAlgCl p inst)
                        (@AlgebraicClosure.instField (@Padic p inst) (@instFieldPadic p inst))))
                    NNReal NNReal.instLinearOrderedCommGroupWithZero (@PadicAlgCl.valued p inst))))))
          i) := by sorry

alias «UpperTheory».«Reformulated».«B».«IntegralPolynomialOverPadicAlgCl».«intMv_X».«» := P2M_UpperTheory_Reformulated_B_IntegralPolynomialOverPadicAlgCl_intMv_X__37500283e46a
