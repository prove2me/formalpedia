-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_Gka4_diag_hermitian
-- name    : UpperTheory.Reformulated.B.Gka4.diag_hermitian
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:00:14.857339+00:00
-- url     : https://prove2.me/theorems/bb373bc8-2e17-4905-b941-784ff5d76b48
-- title:
--   Gka4: diag hermitian
-- statement:
--   The Gka4 construction uses the diag hermitian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/DiagHermitian.lean#L6-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/DiagHermitian.lean#L6-L39

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_HermitianDiagonalisation
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_FixedQuadraticMemBase
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DiagHermitian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.Gka4.diag_hermitian :
    ∀ (F E : Type) [inst : Field F] [inst_1 : NumberField F] [inst_2 : Field E] [inst_3 : NumberField E]
      [inst_4 : Algebra F E] (σ : E →ₐ[F] E),
      HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ →
        ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E),
          HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ T →
            ∃ (g : GL (Fin n) E) (D : Fin n → Fˣ),
              HeckeCharacterZeroLocus.SiegelWeilU.cT (↑σ : E →+* E) (↑g : Matrix (Fin n) (Fin n) E) * T * (↑g : Matrix (Fin n) (Fin n) E) =
                Matrix.diagonal fun (i : Fin n) ↦ (Algebra.algebraMap F E : F → E) (↑(D i) : F) := by sorry
