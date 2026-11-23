-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_etale_exists
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.etale_exists
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:14:37.66982+00:00
-- url     : https://prove2.me/theorems/b2ccfb11-9e1e-4b0b-b201-3bb89ac87b61
-- title:
--   Chart: etale exists
-- statement:
--   The Chart construction uses the etale exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/SpanXLeKerAevalZero.lean#L153-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/SpanXLeKerAevalZero.lean#L153-L202

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_SpanXLeKerAevalZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
open MvPolynomial
variable {R : Type} [CommRing R] {n : ℕ} {S : Type} [CommRing S] [Algebra R S]
  [Algebra (MvPolynomial (Fin n) R) S] [IsScalarTower R (MvPolynomial (Fin n) R) S]
variable [Algebra.FormallyEtale (MvPolynomial (Fin n) R) S] (ε : S →ₐ[R] R)

theorem ReciprocityTheory.ChartRestriction.G.Chart.etale_exists {A : Type} [CommRing A] [Algebra R A] (aug : A →ₐ[R] R)
    (hJ : IsNilpotent (RingHom.ker aug)) (b : Fin n → A) (hb : ∀ j, aug (b j) = ε (sX R j)) :
    ∃ φ : S →ₐ[R] A, aug.comp φ = ε ∧ ∀ j, φ (sX R j) = b j := by sorry
