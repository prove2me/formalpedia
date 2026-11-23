-- Prove2me | Theorems.Thm_PI_WAU_isOpen_Ohat
-- name    : PI.WAU.isOpen_Ohat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:56:16.287689+00:00
-- url     : https://prove2.me/theorems/bc2f0101-f217-436a-82cf-975c6846312d
-- title:
--   WAU: is Open Ohat
-- statement:
--   The WAU construction uses the is Open Ohat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/CartierFrobeniusFormLocal.lean#L101-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/CartierFrobeniusFormLocal.lean#L101-L104

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_CartierFrobeniusFormLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WAU
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Topology
variable {F : Type} [Field F] [NumberField F]

theorem PI.WAU.isOpen_Ohat : IsOpen (Ohat F) := by sorry
