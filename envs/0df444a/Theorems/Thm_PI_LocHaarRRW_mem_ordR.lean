-- Prove2me | Theorems.Thm_PI_LocHaarRRW_mem_ordR
-- name    : PI.LocHaarRRW.mem_ordR
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:35:52.190791+00:00
-- url     : https://prove2.me/theorems/36c69440-a003-5c43-978a-688dd4e80ad3
-- title:
--   Loc Haar RRW: mem ord R
-- statement:
--   The Loc Haar RRW construction uses the mem ord R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalHaarSubgroup/MemOrdR.lean#L16-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalHaarSubgroup/MemOrdR.lean#L16-L23

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

theorem PI.LocHaarRRW.mem_ordR (sg : Formalism.MainNotions.S.Loc.SplitAt A.Fp A.Ep A.cj (Formalism.MainNotions.S.Loc.resChar p)) {x : A.Ep}
    (h1 : (sg.e x).1 ∈ 𝒪[A.Fp]) (h2 : (sg.e x).2 ∈ 𝒪[A.Fp])
    (h12 : Ideal.Quotient.mk (Ideal.span {sg.q}) ⟨(sg.e x).1, h1⟩ =
      Ideal.Quotient.mk (Ideal.span {sg.q}) ⟨(sg.e x).2, h2⟩) :
    x ∈ PI.LocHaarRR.ordR sg := by sorry
