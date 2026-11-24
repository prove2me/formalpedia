-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_Qk24_Mk_mul
-- name    : UpperTheory.Reformulated.B.Qk24.Mk_mul
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:39:20.08036+00:00
-- url     : https://prove2.me/theorems/a897c07c-2933-40cc-a9e3-e6c2c82294e2
-- title:
--   Qk24: Mk mul
-- statement:
--   The Qk24 construction uses the Mk mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SignActionMapComm.lean#L66-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SignActionMapComm.lean#L66-L91

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SignActionMapComm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.Qk24.Mk_mul :
    ∀ {I : Formalism.MainNotions.S.AutInst} {k : ℕ} (b d : Fin k → UpperTheory.Reformulated.B.Qk24.VA I) (η : TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)),
      UpperTheory.Reformulated.B.Qk24.rowM I d * UpperTheory.Reformulated.B.Qk24.colM I b =
          η • (1 : Matrix (Fin k) (Fin k) (TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F))) →
        UpperTheory.Reformulated.B.Qk24.rowM I d * UpperTheory.Reformulated.B.Qk24.colM I d =
            (0 : Matrix (Fin k) (Fin k) (TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F))) →
          UpperTheory.Reformulated.B.Qk24.rowM I b * UpperTheory.Reformulated.B.Qk24.colM I b =
              (0 : Matrix (Fin k) (Fin k) (TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F))) →
            UpperTheory.Reformulated.B.Qk24.rowM I b * UpperTheory.Reformulated.B.Qk24.colM I d =
                (UpperTheory.Reformulated.B.Qk24.sigA I :
                            TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F) → TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F))
                    η •
                  (1 : Matrix (Fin k) (Fin k) (TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F))) →
              ∀ (X Y X' Y' : Matrix (Fin k) (Fin k) (TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F))),
                UpperTheory.Reformulated.B.Qk24.Mk I b d X Y * UpperTheory.Reformulated.B.Qk24.Mk I b d X' Y' =
                  UpperTheory.Reformulated.B.Qk24.Mk I b d
                    (X + X' + X * (η • (1 : Matrix (Fin k) (Fin k) (TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F))) * X'))
                    (Y + Y' +
                      Y *
                        ((UpperTheory.Reformulated.B.Qk24.sigA I :
                                      TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F) → TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F))
                              η •
                            (1 : Matrix (Fin k) (Fin k) (TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F))) *
                          Y')) := by sorry
