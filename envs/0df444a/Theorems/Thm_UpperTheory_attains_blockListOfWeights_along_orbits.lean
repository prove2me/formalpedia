-- Prove2me | Theorems.Thm_UpperTheory_attains_blockListOfWeights_along_orbits
-- name    : UpperTheory.attains_blockListOfWeights_along_orbits
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:13:37.713469+00:00
-- url     : https://prove2.me/theorems/03fa7d7c-1ca5-4106-9d1b-eb8d75140801
-- title:
--   Upper Theory: attains block List Of Weights along orbits
-- statement:
--   The Upper Theory construction uses the attains block List Of Weights along orbits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/OrbitLabellings/AttainsBlockListOfWeightsAlongOrbits.lean#L280-L361
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/OrbitLabellings/AttainsBlockListOfWeightsAlongOrbits.lean#L280-L361

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_OrbitLabellings_RowDefs
import Definitions.Def_Formalism_DropLevelBounds_ThBounds
import Definitions.Def_Formalism_IncomingBounds_IncomingBound
import Definitions.Def_Development_AutomorphicArithmetic_OrbitLabellings_AttainsBlockListOfWeightsAlongOrbits
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Classical
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral UpperTheory.G2
open UpperTheory.G2.RowPlan

theorem UpperTheory.attains_blockListOfWeights_along_orbits :
    RF.CHSupply → RF.MONSupply → ∀ (P : RF.Par) (l : ℕ) (C1 : ℝ), Fintype.card P.Pl = P.f → 1 ≤ P.m → P.m + 3 ≤ P.k → P.r = P.k - 1 + P.m → 5 ≤ l →
    ∀ (Pk : PkgCs P l C1) (y : P.Pl → ZMod P.d → ℕ → ℕ) (u : P.Pl → ZMod P.d → ℕ) (ev : ZMod P.d → ZMod (2 * P.d)),
    (∀ a, Even (ev a).val ∧ (((ev a).val : ℕ) : ZMod P.d) = a) →
    (∀ z ∈ Pk.Z, ∀ a, RF.alongOrb P z Pk.W a = (∑ i ∈ oddLevels P.d, l ^ i * y z a i) +
      (∑ i ∈ oddLevels P.d, y z (a - (i : ZMod P.d)) i) + u z a) →
    (∀ z ∈ Pk.Z, ∀ a i, RF.i0 P.k l ≤ i → y z a i = 0) →
    (∀ (o : {z // z ∈ Pk.Z}) a, ∀ i ∈ oddLevels P.d, y o.1 a i ≠ 0 →
      (RF.GlobalTheory.bi 0 (ev a) i (y o.1 a i)).Attains (Pk.R.X o) (Pk.R.F o) (RF.blockBd l (P.k - 1) P.m i (y o.1 a i))) →
    Pk.ν ≤ (∑ z ∈ Pk.Z, ((∑ a, ∑ i ∈ oddLevels P.d, RF.blockBd l (P.k - 1) P.m i (y z a i)) + ∑ a, RF.chBd l (P.k - 1) P.m (u z a))) +
      Pk.rest / ((l : ℝ) - 1) := by sorry
