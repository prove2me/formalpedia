-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P41_property_optimal_entropy_bound
-- name    : QAlgorithms.Papers.Independent.Extend50.P41.property_optimal_entropy_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:54:29.657596+00:00
-- url     : https://prove2.me/theorems/a03d71a0-3f92-4026-9a1f-79a215e308c7
-- title:
--   Theorem 5.2: fiberwise relative-entropy bound for arbitrary properties
-- statement:
--   Let $d\ge1$, let $\mathcal S$ be the positive semidefinite trace-one matrices on $\mathbb C^d$, including singular matrices, and give $\mathcal S$ its usual matrix topology and Borel sets. Copy counts are positive. A scheme consists of normalized countably additive positive operator measures $E_N$ on $(\mathbb C^d)^{\otimes N}$, fixed independently of the unknown input. Its Born law is $\mu_{N,\rho}(B)=\operatorname{Tr}(\rho^{\otimes N}E_N(B))$. All logarithms are natural.
--
--   Let $X$ be locally compact, separable and metric with its Borel sigma algebra, and let $p:\mathcal S\to X$ be continuous and onto. Let $I_p$ be the pointwise supremum of rates admissible for estimating $p$, with a unique zero at $p(\rho)$ for every input. Then
--   $$I_p(\rho,x)\le\inf_{\sigma\in p^{-1}(x)}D(\sigma\Vert\rho)\qquad(\rho\in\mathcal S,\ x\in X).$$
--   The fibers are nonempty compact sets. The infimum is extended and may be infinite. This turns quantum testing bounds into an upper bound for estimating an arbitrary continuous property.
-- source:
--   Quantum state estimation and large deviations, arXiv:quant-ph/0412053v2, PDF p. 29, Theorem 5.2 / (160)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P41

noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexOrder ENNReal Topology Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Extend50.P41

open QAlgorithms.Tomography (DensityOutcome)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.29-30, Theorem 5.2, (160): continuous surjective property map and
an extended infimum over its compact nonempty fiber. The entropy is D(sigma||rho). -/
theorem property_optimal_entropy_bound {d : ℕ} (hd : 0 < d)
    {X : Type*} [MetricSpace X] [LocallyCompactSpace X] [TopologicalSpace.SeparableSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (p : DensityOutcome d → X) (hp : Continuous p) (honto : Function.Surjective p)
    (rho : DensityOutcome d) (x : X) :
    optimalRate (fun tau y => p tau = y) false rho x ≤
      ⨅ sigma : {sigma : DensityOutcome d // p sigma = x}, QuantumLoss.umegakiEntropy sigma.val.val rho.val sigma.val.property rho.property := by sorry

end QAlgorithms.Papers.Independent.Extend50.P41

end
