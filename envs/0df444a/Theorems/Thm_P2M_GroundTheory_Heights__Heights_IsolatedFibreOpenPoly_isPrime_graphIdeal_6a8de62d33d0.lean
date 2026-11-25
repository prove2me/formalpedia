-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_isPrime_graphIdeal_6a8de62d33d0
-- name    : P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_isPrime_graphIdeal_6a8de62d33d0
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:46:14.023817+00:00
-- url     : https://prove2.me/theorems/e5766977-00ab-4e50-91a9-226de56311ba
-- title:
--   P2 M Ground Theory Heights  Heights Isolated Fibre Open Poly is Prime graph Ideal 6a8de62d33d0: P2 M Ground Theory Heights  Heights Isolated Fibre Open Poly is Prime graph Ideal 6a8de62d33d0
-- statement:
--   The P2 M Ground Theory Heights  Heights Isolated Fibre Open Poly is Prime graph Ideal 6a8de62d33d0 construction uses the P2 M Ground Theory Heights  Heights Isolated Fibre Open Poly is Prime graph Ideal 6a8de62d33d0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PIsolatedFibreOpenPoly.lean#L73-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PIsolatedFibreOpenPoly.lean#L73-L77

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIsolatedFibreOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIsolatedFibreOpenPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIsolatedFibreOpenPoly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Topology Filter Matrix ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.IsolatedFibreOpenPoly
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_isPrime_graphIdeal_6a8de62d33d0 {P : Ideal (MvPolynomial (Fin n) ℂ)} (hP : P.IsPrime)
    (p : Fin d → MvPolynomial (Fin n) ℂ) : (graphIdeal P p).IsPrime := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IsolatedFibreOpenPoly».«isPrime_graphIdeal» := P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_isPrime_graphIdeal_6a8de62d33d0
