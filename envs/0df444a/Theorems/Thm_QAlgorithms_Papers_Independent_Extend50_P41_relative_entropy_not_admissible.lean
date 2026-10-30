-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P41_relative_entropy_not_admissible
-- name    : QAlgorithms.Papers.Independent.Extend50.P41.relative_entropy_not_admissible
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:41:45.785263+00:00
-- url     : https://prove2.me/theorems/e8e4c26a-15b6-409b-b8e9-f310ee91ca3c
-- title:
--   Unnumbered §3.3: relative entropy is not an admissible full rate
-- statement:
--   Let $d\ge1$, let $\mathcal S$ be the positive semidefinite trace-one matrices on $\mathbb C^d$, including singular matrices, and give $\mathcal S$ its usual matrix topology and Borel sets. Copy counts are positive. A scheme consists of normalized countably additive positive operator measures $E_N$ on $(\mathbb C^d)^{\otimes N}$, fixed independently of the unknown input. Its Born law is $\mu_{N,\rho}(B)=\operatorname{Tr}(\rho^{\otimes N}E_N(B))$. All logarithms are natural.
--
--   Assume $d\ge2$. No full-estimation scheme has the entire reversed-argument relative entropy as its LDP rate:
--   $$S\notin\mathcal E(\operatorname{Id}),\qquad S(\rho,\sigma)=D(\sigma\Vert\rho).$$
--   Here admissibility includes a normalized witnessing scheme and a good rate with its unique zero at the input. The dimension guard is necessary because in dimension one the unique-output scheme realizes the zero divergence. This distinguishes an upper envelope from an attainable rate function.
-- source:
--   Quantum state estimation and large deviations, arXiv:quant-ph/0412053v2, PDF p. 9, Unnumbered §3.3 nonadmissibility

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P41

noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexOrder ENNReal Topology Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Extend50.P41

open QAlgorithms.Tomography (DensityOutcome)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.9, §3.3: relative entropy is not an admissible full-estimation rate.
The dimension guard is necessary: d=1 has only one state and zero divergence. -/
theorem relative_entropy_not_admissible {d : ℕ} (hd : 2 ≤ d) :
    ¬ AdmissibleRate (FullTarget (d := d))
      (fun rho sigma => QuantumLoss.umegakiEntropy sigma.val rho.val sigma.property rho.property) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P41

end
