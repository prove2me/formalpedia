-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_residue_algebraMap_7319e467ce67
-- name    : P2M_Formalism_BasicNotions_Examples__LB_residue_algebraMap_7319e467ce67
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T16:34:56.778502+00:00
-- url     : https://prove2.me/theorems/f413a473-5a68-4a75-b4a1-10ffa41ee0ef
-- title:
--   P2 M Formalism Basic Notions Examples  LB residue algebra Map 7319e467ce67: P2 M Formalism Basic Notions Examples  LB residue algebra Map 7319e467ce67
-- statement:
--   The P2 M Formalism Basic Notions Examples  LB residue algebra Map 7319e467ce67 construction uses the P2 M Formalism Basic Notions Examples  LB residue algebra Map 7319e467ce67 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocF.lean#L11-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocF.lean#L11-L23

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocE
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.LB
open NumberField IsDedekindDomain Polynomial IsLocalRing Formalism.BasicNotions Formalism.BasicNotions.Loc
variable {l : ℕ} [hl : Fact l.Prime] (LL : FinExt l)

theorem P2M_Formalism_BasicNotions_Examples__LB_residue_algebraMap_7319e467ce67 (c : ℤ_[l]) :
    residue ↥(OL LL) (algebraMap ℤ_[l] ↥(OL LL) c) = (((PadicInt.toZMod c).val : ℕ) : ResidueField ↥(OL LL)) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«LB».«residue_algebraMap» := P2M_Formalism_BasicNotions_Examples__LB_residue_algebraMap_7319e467ce67
