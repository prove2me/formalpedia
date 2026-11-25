-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_ApproximationIntegralOutsideFinset_approxF
-- name    : UpperTheory.Reformulated.B.ApproximationIntegralOutsideFinset.approxF
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T06:08:39.913096+00:00
-- url     : https://prove2.me/theorems/29381240-a0b4-545a-9bab-e16dfdd4fae2
-- title:
--   Approximation Integral Outside Finset: approx F
-- statement:
--   The Approximation Integral Outside Finset construction uses the approx F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SimpLemmas.lean#L90-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SimpLemmas.lean#L90-L125

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SimpLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain ValuativeRel nonZeroDivisors

theorem UpperTheory.Reformulated.B.ApproximationIntegralOutsideFinset.approxF :
    ∀ {F E : Type} [inst : Field F] [inst_1 : NumberField F] [inst_2 : Field E] [inst_3 : NumberField E]
      [inst_4 : Algebra F E] {sig : E →ₐ[F] E}
      (A : (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) → Formalism.MainNotions.S.Loc.LocAt F E sig p)
      (S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) (c : NumberField.RingOfIntegers F),
      c ≠ (0 : NumberField.RingOfIntegers F) →
        ∀ (b : (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) → (A p).Fp),
          ∃ (f : F),
            (∀ p ∈ S,
                (ValuativeRel.valuation (A p).Fp : (A p).Fp → ValuativeRel.ValueGroupWithZero (A p).Fp)
                    (((A p).ιF : F → (A p).Fp) f - b p) ≤
                  (ValuativeRel.valuation (A p).Fp : (A p).Fp → ValuativeRel.ValueGroupWithZero (A p).Fp)
                    (((A p).ιF : F → (A p).Fp)
                      ((Algebra.algebraMap (NumberField.RingOfIntegers F) F : NumberField.RingOfIntegers F → F) c))) ∧
              ∀ p ∉ S, ((A p).ιF : F → (A p).Fp) f ∈ (ValuativeRel.valuation (A p).Fp).integer := by sorry
