-- Prove2me | Theorems.Thm_P2M_Formalism_L2_SG_Pf_LatDictZ_Z0_BR_algebraMap_ne_zero__8e24046a48f0
-- name    : P2M_Formalism_L2_SG_Pf_LatDictZ_Z0_BR_algebraMap_ne_zero__8e24046a48f0
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:57:58.976577+00:00
-- url     : https://prove2.me/theorems/ddb50289-1b98-4f51-b93d-31f908b51132
-- title:
--   P2 M Formalism L2 SG Pf Lat Dict Z Z0 BR algebra Map ne zero  8e24046a48f0: P2 M Formalism L2 SG Pf Lat Dict Z Z0 BR algebra Map ne zero  8e24046a48f0
-- statement:
--   The P2 M Formalism L2 SG Pf Lat Dict Z Z0 BR algebra Map ne zero  8e24046a48f0 construction uses the P2 M Formalism L2 SG Pf Lat Dict Z Z0 BR algebra Map ne zero  8e24046a48f0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SelfDualUnimodular/LocalLatticeDictionary/AlgebraMapNeZero.lean#L34-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SelfDualUnimodular/LocalLatticeDictionary/AlgebraMapNeZero.lean#L34-L36

import Mathlib
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_UnimodOfSelfDual
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_AlgebraMapNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z0 Formalism.L2.SG.Pf.LatDictZ.Z0.BR
open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA PIW.AdelClassFin
variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem P2M_Formalism_L2_SG_Pf_LatDictZ_Z0_BR_algebraMap_ne_zero__8e24046a48f0 {p : Ideal (𝓞 E)} (hp : p.IsPrime) {t : 𝓞 E}
    (ht : t ∈ Formalism.HermitianLatticesTheory.hcompl (K := E) p) : algebraMap (𝓞 E) E t ≠ 0 := by sorry

alias «Formalism».«L2».«SG».«Pf».«LatDictZ».«Z0».«BR».«algebraMap_ne_zero'» := P2M_Formalism_L2_SG_Pf_LatDictZ_Z0_BR_algebraMap_ne_zero__8e24046a48f0
