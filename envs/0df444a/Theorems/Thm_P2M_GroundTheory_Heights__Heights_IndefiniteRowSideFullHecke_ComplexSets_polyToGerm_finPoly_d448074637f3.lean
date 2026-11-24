-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_polyToGerm_finPoly_d448074637f3
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_polyToGerm_finPoly_d448074637f3
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:47:08.236475+00:00
-- url     : https://prove2.me/theorems/0efda405-9ceb-4875-9e6b-9a91289e8dbb
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets poly To Germ fin Poly d448074637f3: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets poly
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets poly To Germ fin Poly d448074637f3 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets poly To Germ fin Poly d448074637f3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/WeierstrassPolynomialRing.lean#L58-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/WeierstrassPolynomialRing.lean#L58-L74

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_WeierstrassRemainderUnique
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAnalyticGermsNoetherian
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHolGermsDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_WeierstrassPolynomialRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter Polynomial
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_polyToGerm_finPoly_d448074637f3 {σ : Type} [Fintype σ] {d : ℕ} (a : Fin d → (σ → ℂ) → ℂ)
    (ha : ∀ j, AnalyticAt ℂ (a j) 0) :
    ((polyToGerm σ (finPoly fun j => mkGerm (a j) (ha j)) : holGerms (0 : Option σ → ℂ)) :
      Germ (𝓝 (0 : Option σ → ℂ)) ℂ) =
      ↑(fun x : Option σ → ℂ => ∑ j : Fin d, a j (fun i => x (some i)) * x none ^ (j : ℕ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«polyToGerm_finPoly» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_polyToGerm_finPoly_d448074637f3
