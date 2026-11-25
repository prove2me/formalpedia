-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_Qf29_der_aeval
-- name    : UpperTheory.Reformulated.B.Qf29.der_aeval
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T01:27:53.335067+00:00
-- url     : https://prove2.me/theorems/8c48d1e7-b8cd-4590-8b7e-3e8bcc97564f
-- title:
--   Qf29: der aeval
-- statement:
--   The Qf29 construction uses the der aeval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/DerAeval.lean#L4-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/DerAeval.lean#L4-L41

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PowMapMemOfPowMulMem
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DerAeval
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.Qf29.der_aeval :
    ∀ {F : Type} [inst : Field F] {δ : F → F},
      Formalism.L2.Pj.GenericSectionMinimum.IsDer δ →
        ∀ {E : Type} [inst_1 : CommRing E] [inst_2 : Algebra E F],
          (∀ (e : E), δ ((Algebra.algebraMap E F : E → F) e) = (0 : F)) →
            ∀ {σ : Type} [inst_3 : Fintype σ] [DecidableEq σ] (t : σ → F) (P : MvPolynomial σ E),
              δ ((MvPolynomial.aeval t : MvPolynomial σ E → F) P) =
                ∑ i : σ,
                  (MvPolynomial.aeval t : MvPolynomial σ E → F)
                      ((MvPolynomial.pderiv i : MvPolynomial σ E → MvPolynomial σ E) P) *
                    δ (t i) := by sorry
