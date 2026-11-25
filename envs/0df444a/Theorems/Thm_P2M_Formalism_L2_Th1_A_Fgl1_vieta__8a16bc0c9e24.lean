-- Prove2me | Theorems.Thm_P2M_Formalism_L2_Th1_A_Fgl1_vieta__8a16bc0c9e24
-- name    : P2M_Formalism_L2_Th1_A_Fgl1_vieta__8a16bc0c9e24
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:57:15.077993+00:00
-- url     : https://prove2.me/theorems/ba35d0b5-729c-44c1-bdba-b2dfe581d5a2
-- title:
--   P2 M Formalism L2 Th1 A Fgl1 vieta  8a16bc0c9e24: P2 M Formalism L2 Th1 A Fgl1 vieta  8a16bc0c9e24
-- statement:
--   The P2 M Formalism L2 Th1 A Fgl1 vieta  8a16bc0c9e24 construction uses the P2 M Formalism L2 Th1 A Fgl1 vieta  8a16bc0c9e24 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/FormalGroupEqWSeries.lean#L162-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/FormalGroupEqWSeries.lean#L162-L175

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementG
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupEqWSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.Fgl1
local notation "L" i => MvPowerSeries.coeff (Finsupp.single i 1)
local notation "cc" => MvPowerSeries.constantCoeff
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
open Formalism.ELL.WeierstrassChordSeries

theorem P2M_Formalism_L2_Th1_A_Fgl1_vieta__8a16bc0c9e24 {A : Type*} [CommRing A] {a1 a2 a3 a4 a6 l n z1 z2 z3 : A}
    (hz : ∀ f : A, f * (z1 - z2) = 0 → f = 0)
    (h1 : G a1 a2 a3 a4 a6 z1 (l * z1 + n) = 0) (h2 : G a1 a2 a3 a4 a6 z2 (l * z2 + n) = 0)
    (he1 : c3 a2 a4 a6 l * (z1 + z2 + z3) + c2 a1 a2 a3 a4 a6 l n = 0) :
    G a1 a2 a3 a4 a6 z3 (l * z3 + n) = 0 := by sorry

alias «Formalism».«L2».«Th1».«A».«Fgl1».«vieta'» := P2M_Formalism_L2_Th1_A_Fgl1_vieta__8a16bc0c9e24
