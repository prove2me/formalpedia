-- Prove2me | Theorems.Thm_P2M_Formalism_L2_Pj_GenSect_Phi_mk__spec_b1aeb19d49e4
-- name    : P2M_Formalism_L2_Pj_GenSect_Phi_mk__spec_b1aeb19d49e4
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:37:35.996969+00:00
-- url     : https://prove2.me/theorems/38ee6b29-b492-5cab-86a3-188d3d8de0b4
-- title:
--   P2 M Formalism L2 Pj Gen Sect Phi mk  spec b1aeb19d49e4: P2 M Formalism L2 Pj Gen Sect Phi mk  spec b1aeb19d49e4
-- statement:
--   The P2 M Formalism L2 Pj Gen Sect Phi mk  spec b1aeb19d49e4 construction uses the P2 M Formalism L2 Pj Gen Sect Phi mk  spec b1aeb19d49e4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSectC.lean#L40-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSectC.lean#L40-L46

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSectB
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSectC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.GenSect
open MvPolynomial
open scoped TensorProduct
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D m : ℕ}

theorem P2M_Formalism_L2_Pj_GenSect_Phi_mk__spec_b1aeb19d49e4 (x : Fin m → Ω) (j₀ : Fin m)
    (hinj : ∀ q : KT K D m, q ≠ 0 → aeval (gs x j₀) q ≠ 0) (a : ΩT Ω D m) (y : KTS K Ω D m)
    (v : FractionRing (CT Ω D j₀)) :
    Phi x j₀ hinj (IsLocalization.mk' (RS K Ω D m) a y) = v ↔
      algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (psi x j₀ a) =
        algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (psi x j₀ y) * v := by sorry

alias «Formalism».«L2».«Pj».«GenSect».«Phi_mk'_spec» := P2M_Formalism_L2_Pj_GenSect_Phi_mk__spec_b1aeb19d49e4
