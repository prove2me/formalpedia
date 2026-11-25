-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_QuotExtension_orth_sub_d589be79082f
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_QuotExtension_orth_sub_d589be79082f
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:40:11.383705+00:00
-- url     : https://prove2.me/theorems/0a140ace-7b50-4383-855b-9410df25dc83
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels S6 Quot Extension orth sub d589be79082f: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels S6 Quot E
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels S6 Quot Extension orth sub d589be79082f construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels S6 Quot Extension orth sub d589be79082f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ExistsSmulMemIdealLattice.lean#L122-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ExistsSmulMemIdealLattice.lean#L122-L146

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsTer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ExistsSmulMemIdealLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
open NumberField NumberField.ComplexEmbedding TensorProduct Matrix GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.ComplexAt
open scoped nonZeroDivisors ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels.S6 GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels.S6.QuotExtension
variable {K : Type} [Field K] [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_QuotExtension_orth_sub_d589be79082f {n m : ℕ} {a : Fin n → FractionalIdeal (𝓞 K)⁰ K} (ha : ∀ x, a x ≠ 0)
    {d : (K →+* ℂ) → Fin n → ℝ} (hd : ∀ σ x, 0 < d σ x) (hc : ∀ σ x, d (conjugate σ) x = d σ x)
    (b : Fin m → Fin n → K) (σ : K →+* ℂ) (y : Fibre σ (idealLattice a))
    (hy : ∀ w : Fibre σ (subLattice a b), ((latticeBundle a d hd hc).metric.form σ).inner
      ((subLattice a b).subtype.lTensor (ComplexAt σ) w) y = 0) (i : Fin m) :
    star (embVec σ (b i)) ⬝ᵥ (diagMetric d σ *ᵥ latticeCoord σ (idealLattice a) y) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Kernels».«S6».«QuotExtension».«orth_sub» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_QuotExtension_orth_sub_d589be79082f
