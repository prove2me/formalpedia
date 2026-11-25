-- Prove2me | Theorems.Thm_PI_QnHermHaar_relX
-- name    : PI.QnHermHaar.relX
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:47:51.313281+00:00
-- url     : https://prove2.me/theorems/7e5e577f-9755-568e-91a4-776365830cfb
-- title:
--   Qn Herm Haar: rel X
-- statement:
--   The Qn Herm Haar construction uses the rel X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/SumFourCommVersion.lean#L153-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/SumFourCommVersion.lean#L153-L167

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_LowerRightNeZeroOfUpperRightZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_SumFourCommVersion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.QnHermHaar
open Formalism.REAL Formalism.FourierDecayAlt.Q

theorem PI.QnHermHaar.relX {m : ℕ} (x xb : Fin m → ℂ) (Hm P Q : Matrix (Fin m) (Fin m) ℂ) (ε : Fin m → ℤˣ)
    (hxb : ∀ c, xb c = ∑ l, Hm l c * star (x l)) (hQ : ∀ i j, star (Q i j) = P j i)
    (hHP : ∀ k b, ∑ j, Hm k j * P j b = P k b * ((ε b : ℤ) : ℂ)) (c : Fin m) :
    (xb ᵥ* P) c = ((ε c : ℤ) : ℂ) * star ((Q *ᵥ x) c) := by sorry
