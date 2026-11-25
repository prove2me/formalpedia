-- Prove2me | Theorems.Thm_PI_LocHaarRRW_ordR_sub
-- name    : PI.LocHaarRRW.ordR_sub
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:35:17.488358+00:00
-- url     : https://prove2.me/theorems/98fc8cc5-f0ec-5e9d-9d2f-e0efe8e10fa1
-- title:
--   Loc Haar RRW: ord R sub
-- statement:
--   The Loc Haar RRW construction uses the ord R sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalHaarSubgroup/MemOrdR.lean#L25-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalHaarSubgroup/MemOrdR.lean#L25-L32

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocHaarRR
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalHaarSubgroup_IntegralMemNhdsAndSubsetCompactOfFinrankTwo
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalHaarSubgroup_MemOrdR
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel MeasureTheory Topology IsDedekindDomain NumberField
open PI PI.LocHaarRRW
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} {A : Formalism.MainNotions.S.Loc.LocAt F E sig p}

theorem PI.LocHaarRRW.ordR_sub (sg : Formalism.MainNotions.S.Loc.SplitAt A.Fp A.Ep A.cj (Formalism.MainNotions.S.Loc.resChar p)) {x : A.Ep}
    (hx : x ∈ PI.LocHaarRR.ordR sg) : (sg.e x).1 ∈ 𝒪[A.Fp] ∧ (sg.e x).2 ∈ 𝒪[A.Fp] := by sorry
