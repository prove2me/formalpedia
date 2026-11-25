-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_IntertwinerStructure_intw_sum
-- name    : UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T06:30:00.145261+00:00
-- url     : https://prove2.me/theorems/2b4e4340-1131-484e-bbe4-39f3007e0e3a
-- title:
--   Intertwiner Structure: intw sum
-- statement:
--   The Intertwiner Structure construction uses the intw sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/IntertwinerStructure.lean#L31-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/IntertwinerStructure.lean#L31-L53

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementMA
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreCut
import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGaugeCut
import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IntertwinerStructure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum :
    ∀ {Wp Wq : Type} [inst : NormedAddCommGroup Wp] [inst_1 : InnerProductSpace ℂ Wp] [inst_2 : NormedAddCommGroup Wq]
      [inst_3 : InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [inst_5 : FiniteDimensional ℂ Wq] {P : Formalism.FourierDecayAlt.M.Par}
      {Bs : Formalism.FourierDecayAlt.B.RealPlaceData P.k P.r Wp Wq} {e : Formalism.FourierDecayAlt.M.Ty P → ℂ → Wq →L[ℂ] Wp},
      (∀ (Φ : ↥(Formalism.FourierDecayAlt.Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) (ρ : Formalism.FourierDecayAlt.M.Ty P),
          Formalism.FourierDecayAlt.P.CutMP.Gauge.rawR P Bs.μsec e (↑Φ : Formalism.FourierDecayAlt.Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ ∈
            Formalism.FourierDecayAlt.MA.smSub P.r P.TT) →
        ∀ {ι : Type} (s : Finset ι) {A : ι → Formalism.FourierDecayAlt.Q.Pr ↥(Formalism.FourierDecayAlt.Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')}
          {A' : ι → Formalism.FourierDecayAlt.MA.A P (Formalism.FourierDecayAlt.MA.DQ P)},
          (∀ i ∈ s, UpperTheory.Reformulated.B.IntertwinerStructure.Intw P Bs e (A i) (A' i)) → UpperTheory.Reformulated.B.IntertwinerStructure.Intw P Bs e (∑ i ∈ s, A i) (∑ i ∈ s, A' i) := by sorry
