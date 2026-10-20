-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P45_dampingOptimizedLimits
-- name    : QAlgorithms.Papers.Independent.Dependency50.P45.dampingOptimizedLimits
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T17:08:52.036645+00:00
-- url     : https://prove2.me/theorems/3df19ee9-47f1-44f2-88d4-b14a53f4bfee
-- title:
--   §III.B: optimized damping ratio and maximizing input parameters
-- statement:
--   Let $\mathcal D_p$ be qubit amplitude damping. Let $J_E(p,x)=h_2(x)+h_2((1-p)x)-h_2(px)$ and let $J_H(p,x)$ be the Holevo information of the equiprobable pure signal pair with diagonal $(1-x,x)$ and off-diagonals $\pm\sqrt{x(1-x)}$. Maximizers on $[0,1]$ exist for every $0\le p<1$, and maximizing selectors $x_E(p),x_H(p)$ can be chosen simultaneously. For every such choice,
--
--   $$\lim_{p\uparrow1}x_E(p)=1,\qquad \lim_{p\uparrow1}x_H(p)=\tfrac12,\qquad \lim_{p\uparrow1}\frac{C_E(\mathcal D_p)}{C_H(\mathcal D_p)}=4.$$
--
--   Here $C_E$ is operational with unlimited prior EPR pairs and uniform message error, while $C_H$ is the single-use Holevo capacity over all finite input ensembles. Entropies and rates are in bits; the endpoint $p=1$, where both capacities vanish, is excluded from the limit domain.
-- source:
--   Entanglement-assisted capacity of a quantum channel and the reverse Shannon theorem, arXiv:quant-ph/0106052v2, PDF p. 35, §III.B: optimized damping ratio and maximizing input parameters

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P45

noncomputable section

open scoped ComplexConjugate Matrix

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Dependency50.P45

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)

open QAlgorithms.Papers.Independent.Information100.P76 (dampingChannel)

/-- PDF p.35: selectors exist and all choices tend to 1 and 1/2;
operational CE divided by single-use Holevo capacity tends to four. -/
theorem dampingOptimizedLimits :
    (∃ f g : ℝ → ℝ, ∀ p ∈ Set.Ico (0 : ℝ) 1,
      MaximizesOnUnit (dampingEAObjective p) (f p) ∧
      MaximizesOnUnit (dampingHolevoObjective p) (g p)) ∧
    (∀ f g : ℝ → ℝ, (∀ p ∈ Set.Ico (0 : ℝ) 1,
      MaximizesOnUnit (dampingEAObjective p) (f p) ∧
      MaximizesOnUnit (dampingHolevoObjective p) (g p)) →
      Tendsto f (nhdsWithin 1 (Set.Ico (0 : ℝ) 1)) (nhds 1) ∧
      Tendsto g (nhdsWithin 1 (Set.Ico (0 : ℝ) 1)) (nhds (1 / 2))) ∧
    Tendsto (fun p => resourceCapacity standardEbit (dampingChannel p 1) / holevoCapacity (dampingChannel p 1))
      (nhdsWithin 1 (Set.Ico (0 : ℝ) 1)) (nhds 4) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P45

end
