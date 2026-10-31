-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P14_absolute_quantitative_regularization
-- name    : QAlgorithms.Papers.Independent.Intake100.P14.absolute_quantitative_regularization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:16:39.681548+00:00
-- url     : https://prove2.me/theorems/21d6f1e5-9c3a-4a42-af39-acf3d1a3b76e
-- title:
--   Proposition 36: absolute quantitative regularization
-- statement:
--   There exist positive sequences $(\eta_p)_{p\ge0}$ and $(C_p)_{p\ge0}$, independent of all groups, modules, actions and metrics, with the following property. Let $G$ be a compact Hausdorff second countable group with probability Haar measure, and let $(A,\rho,T)$ be a Polish Abelian $G$-module whose compatible metric is translation invariant and action invariant. Let $p\ge1$ and $0<\varepsilon\le\eta_p$. If the Borel cocycle $\psi:G^p\to A$ is $\varepsilon$-small, then there are a Borel $(p-1)$-cochain $\lambda$ and a Borel $p$-cocycle $\phi$ such that
--
--   $$\psi=\phi+d\lambda\quad\text{a.e.},\qquad \lambda\text{ is }C_p\varepsilon^{2^{-p}}\text{-small},\qquad \rho_\infty(0,\phi)\le C_p\varepsilon^{2^{-p}}.$$
--
--   Here smallness means the strict tail-measure bound in Section 2 and $\rho_\infty$ is the extended-valued uniform essential distance. This gives uniform quantitative regularization in each degree.
-- source:
--   Continuity properties of measurable group cohomology, arXiv:1004.4937v4, PDF p. 16, Proposition 36: absolute quantitative regularization

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P14

noncomputable section

open MeasureTheory Filter Set

open scoped BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intake100.P14

universe u v w

/-- Proposition 36, PDF pp.16--17: positive universal threshold and bound sequences,
chosen before every group, coefficient group, metric, action and cocycle. The exponent
is epsilon^(2^(-p)), as confirmed in the PDF. -/
theorem absolute_quantitative_regularization :
    ∃ eta C : ℕ → ℝ, (∀ p, 0 < eta p ∧ 0 < C p) ∧
      ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
        [T2Space G] [CompactSpace G] [SecondCountableTopology G]
        [MeasurableSpace G] [BorelSpace G]
        (A : Type v) [AddCommGroup A] [MetricSpace A] [IsTopologicalAddGroup A]
        [PolishSpace A] [MeasurableSpace A] [BorelSpace A]
        (mu : Measure G) [mu.IsHaarMeasure] [IsProbabilityMeasure mu]
        (T : ModuleAction G A), ActionIsometric T →
        QuantitativeRegularization mu T.act eta C := by sorry

end QAlgorithms.Papers.Independent.Intake100.P14

end
