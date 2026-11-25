-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolyDerivationsDetectSquare_of_perfectField_7842d31f3c27
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolyDerivationsDetectSquare_of_perfectField_7842d31f3c27
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:20:13.009111+00:00
-- url     : https://prove2.me/theorems/5135546c-43f5-53ca-972b-b7b571f977f6
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Poly Derivations Detect Square of perfect Field 7842d31f3c27: P2 M Ground Theory Heights  Heights Indefinite Row Side Fu
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Poly Derivations Detect Square of perfect Field 7842d31f3c27 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Poly Derivations Detect Square of perfect Field 7842d31f3c27 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPolyDerivationsDetectSquare.lean#L13-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPolyDerivationsDetectSquare.lean#L13-L58

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPolyDerivationsDetectSquare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPerfectFieldExtensionFormallySmooth
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPolyKaehlerFree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPolyDerivationsDetectSquare
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
noncomputable section
open IsLocalRing KaehlerDifferential TensorProduct

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolyDerivationsDetectSquare_of_perfectField_7842d31f3c27
    (h₁ : PerfectFieldExtensionFormallySmooth.Statement) (h₂ : PolyKaehlerFree.Statement)
    (F k : Type) [Field F] [Field k] [Algebra F k] [PerfectField F] (n : ℕ)
    (p : Ideal (MvPolynomial (Fin n) k)) [p.IsPrime] (g : MvPolynomial (Fin n) k) (hg : g ∈ p)
    (hD : ∀ D : Derivation ℤ (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) k), D g ∈ p) :
    algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime p) g ∈
      maximalIdeal (Localization.AtPrime p) ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«PolyDerivationsDetectSquare».«of_perfectField» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolyDerivationsDetectSquare_of_perfectField_7842d31f3c27
