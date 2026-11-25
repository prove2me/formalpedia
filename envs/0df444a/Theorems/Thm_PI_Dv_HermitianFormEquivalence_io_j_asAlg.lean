-- Prove2me | Theorems.Thm_PI_Dv_HermitianFormEquivalence_io_j_asAlg
-- name    : PI.Dv.HermitianFormEquivalence.io_j_asAlg
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:28:00.805874+00:00
-- url     : https://prove2.me/theorems/a9507a15-e74a-49ed-9334-f02e0f6e907a
-- title:
--   Hermitian Form Equivalence: io j as Alg
-- statement:
--   The Hermitian Form Equivalence construction uses the io j as Alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TraceFormEquality/FormEqImage.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TraceFormEquality/FormEqImage.lean#L16-L20

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TraceFormEquality_ExistsSumEqOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TraceFormEquality_FormEqImage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.HermitianFormEquivalence
open PI.Dv
variable {K : Type} [Field K] {σ : K →+* ℂ} {G : Type} [Group G] [Fintype G] {T : GoodSet K G}
  {EE : Type} [AddCommGroup EE] [Module ℂ EE] {ρE : Representation ℂ G EE}

theorem PI.Dv.HermitianFormEquivalence.io_j_asAlg (M : GMap K σ G T EE ρE) (a : MonoidAlgebra K G) (x : M.VK) :
    M.io (M.j (M.rhoK.asAlgebraHom a x)) = ∑ g : G, σ (a.coeff g) • ρE g (M.io (M.j x)) := by sorry
