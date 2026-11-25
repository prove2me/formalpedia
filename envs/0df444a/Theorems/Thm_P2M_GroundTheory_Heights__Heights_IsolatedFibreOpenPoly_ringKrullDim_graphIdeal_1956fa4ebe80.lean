-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_ringKrullDim_graphIdeal_1956fa4ebe80
-- name    : P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_ringKrullDim_graphIdeal_1956fa4ebe80
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:45:34.194888+00:00
-- url     : https://prove2.me/theorems/846e8f79-4a53-4f8f-b1e8-5c131d41cec5
-- title:
--   P2 M Ground Theory Heights  Heights Isolated Fibre Open Poly ring Krull Dim graph Ideal 1956fa4ebe80: P2 M Ground Theory Heights  Heights Isolated Fibre Open Poly ring Krull Dim graph Ideal 1956fa4ebe
-- statement:
--   The P2 M Ground Theory Heights  Heights Isolated Fibre Open Poly ring Krull Dim graph Ideal 1956fa4ebe80 construction uses the P2 M Ground Theory Heights  Heights Isolated Fibre Open Poly ring Krull Dim graph Ideal 1956fa4ebe80 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PIsolatedFibreOpenPoly.lean#L79-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PIsolatedFibreOpenPoly.lean#L79-L90

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

theorem P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_ringKrullDim_graphIdeal_1956fa4ebe80 (P : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin d → MvPolynomial (Fin n) ℂ) :
    ringKrullDim (MvPolynomial (Fin (n + d)) ℂ ⧸ graphIdeal P p) =
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ P) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IsolatedFibreOpenPoly».«ringKrullDim_graphIdeal» := P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_ringKrullDim_graphIdeal_1956fa4ebe80
