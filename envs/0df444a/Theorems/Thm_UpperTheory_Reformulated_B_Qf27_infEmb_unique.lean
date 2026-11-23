-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_Qf27_infEmb_unique
-- name    : UpperTheory.Reformulated.B.Qf27.infEmb_unique
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:34:21.821978+00:00
-- url     : https://prove2.me/theorems/b1a8d01a-e0c5-4d50-8e4f-cf0d68624a8e
-- title:
--   Qf27: inf Emb unique
-- statement:
--   The Qf27 construction uses the inf Emb unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/InfEmbUnique.lean#L38-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/InfEmbUnique.lean#L38-L64

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_InfEmbUnique
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.Qf27.infEmb_unique :
    ∀ {F E : Type} [inst : Field F] [NumberField F] [inst_2 : Field E] [inst_3 : Algebra F E] {τ : E →+* ℂ}
      {θ θ' : TensorProduct F (UpperTheory.Reformulated.B.Qf27.Ainf F) E →+* ℂ},
      UpperTheory.Reformulated.B.Qf27.IsInfEmb τ θ → UpperTheory.Reformulated.B.Qf27.IsInfEmb τ θ' → θ = θ' := by sorry
