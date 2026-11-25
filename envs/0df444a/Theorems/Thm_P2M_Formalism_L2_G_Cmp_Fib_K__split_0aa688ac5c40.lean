-- Prove2me | Theorems.Thm_P2M_Formalism_L2_G_Cmp_Fib_K__split_0aa688ac5c40
-- name    : P2M_Formalism_L2_G_Cmp_Fib_K__split_0aa688ac5c40
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:57:48.900343+00:00
-- url     : https://prove2.me/theorems/f4102ed1-b4f2-4e94-856e-62111590a748
-- title:
--   P2 M Formalism L2 G Cmp Fib K  split 0aa688ac5c40: P2 M Formalism L2 G Cmp Fib K  split 0aa688ac5c40
-- statement:
--   The P2 M Formalism L2 G Cmp Fib K  split 0aa688ac5c40 construction uses the P2 M Formalism L2 G Cmp Fib K  split 0aa688ac5c40 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/ComparisonMaps/ClsFib.lean#L25-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/ComparisonMaps/ClsFib.lean#L25-L29

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_ComparisonMaps_ClsFib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Cmp
open Formalism.UG
open Formalism.L2.G.Cmp.Fib
variable {G Gp : Type} [Group G] [Group Gp] {K K' : Subgroup G} {Kp : Subgroup Gp} (X : Fib K K' Kp) (H : Subgroup G)

theorem P2M_Formalism_L2_G_Cmp_Fib_K__split_0aa688ac5c40 (x : G) (hx : x ∈ K') : (X.j (X.pr x))⁻¹ * x ∈ K := by sorry

alias «Formalism».«L2».«G».«Cmp».«Fib».«K'_split» := P2M_Formalism_L2_G_Cmp_Fib_K__split_0aa688ac5c40
