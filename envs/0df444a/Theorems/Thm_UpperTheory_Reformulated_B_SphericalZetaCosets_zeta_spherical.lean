-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_SphericalZetaCosets_zeta_spherical
-- name    : UpperTheory.Reformulated.B.SphericalZetaCosets.zeta_spherical
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:29:09.854211+00:00
-- url     : https://prove2.me/theorems/43caacf6-543c-4bcb-8c37-f6ee39cdcebc
-- title:
--   Spherical Zeta Cosets: zeta spherical
-- statement:
--   The Spherical Zeta Cosets construction uses the zeta spherical property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SphericalZetaCosets.lean#L292-L439
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SphericalZetaCosets.lean#L292-L439

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_GroundTheory_LocalFields_PadicLogSeries
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SphericalZetaCosets
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped ValuativeRel
open UpperTheory.Reformulated.B.SphericalZetaCosets

theorem UpperTheory.Reformulated.B.SphericalZetaCosets.zeta_spherical :
    ∀ {F : Type} [inst : Field F] [inst_1 : ValuativeRel F] [inst_2 : TopologicalSpace F]
      [inst_3 : IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ},
      GlobalTheory.CompanionTheory.QL.LF O ϖ nrm q →
        ∀ {c : ℕ} (χ : Fin c → F → ℂ) (α : Fin c → ℂ),
          GlobalTheory.CompanionTheory.QL.UnrChar nrm q χ α →
            ∀ (φ : GL (Fin c) F → ℂ),
              GlobalTheory.CompanionTheory.QL.IsSphFn O nrm χ φ →
                ∀ (κ : MeasureTheory.Measure (GL (Fin c) F)),
                  κ.IsMulLeftInvariant →
                    (κ : Set (GL (Fin c) F) → ENNReal) (↑(GlobalTheory.CompanionTheory.QL.GLint O c) : Set (GL (Fin c) F)) = (1 : ENNReal) →
                      ∀ (σ : ℝ),
                        (∀ (i : Fin c), ‖α i‖ * (↑q : ℝ) ^ (((↑c : ℝ) - (1 : ℝ)) / (2 : ℝ) - σ) < (1 : ℝ)) →
                          MeasureTheory.IntegrableOn
                              (fun (g : GL (Fin c) F) ↦
                                φ g * (↑((nrm : F → ℝ) (↑g : Matrix (Fin c) (Fin c) F).det ^ σ) : ℂ))
                              (GlobalTheory.CompanionTheory.QL.Mint O c) κ ∧
                            ∫ (g : GL (Fin c) F) in GlobalTheory.CompanionTheory.QL.Mint O c,
                                φ g * (↑((nrm : F → ℝ) (↑g : Matrix (Fin c) (Fin c) F).det ^ σ) : ℂ) ∂κ =
                              ∏ i : Fin c, ((1 : ℂ) - α i * (↑((↑q : ℝ) ^ (((↑c : ℝ) - (1 : ℝ)) / (2 : ℝ) - σ)) : ℂ))⁻¹ := by sorry
