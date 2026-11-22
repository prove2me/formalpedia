-- Prove2me | Theorems.Thm_P2M_Formalism_L2_Pj_FJ_emb_cc__a0a14d96c40b
-- name    : P2M_Formalism_L2_Pj_FJ_emb_cc__a0a14d96c40b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T18:07:48.788704+00:00
-- url     : https://prove2.me/theorems/dfc6ba94-e613-4b89-950c-c3fac7271952
-- title:
--   P2 M Formalism L2 Pj FJ emb cc  a0a14d96c40b: P2 M Formalism L2 Pj FJ emb cc  a0a14d96c40b
-- statement:
--   The P2 M Formalism L2 Pj FJ emb cc  a0a14d96c40b construction uses the P2 M Formalism L2 Pj FJ emb cc  a0a14d96c40b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/RdOrbIntOfLatZ.lean#L81-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/RdOrbIntOfLatZ.lean#L81-L81

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntegrableOnIntegrand
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ChartRestriction.G.FD NumberField Matrix
open scoped ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.FJ
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}

theorem P2M_Formalism_L2_Pj_FJ_emb_cc__a0a14d96c40b (τ : E →+* ℂ) (x : E) : τ (cc x) = conj (τ x) := by sorry

alias «Formalism».«L2».«Pj».«FJ».«emb_cc'» := P2M_Formalism_L2_Pj_FJ_emb_cc__a0a14d96c40b
