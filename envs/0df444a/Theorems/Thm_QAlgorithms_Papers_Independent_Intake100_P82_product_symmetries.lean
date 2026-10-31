-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P82_product_symmetries
-- name    : QAlgorithms.Papers.Independent.Intake100.P82.product_symmetries
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:16:14.547993+00:00
-- url     : https://prove2.me/theorems/5a517e51-0c7b-4495-a16b-6e040b23d8ee
-- title:
--   Example 3.4: product constructions for commutation and reversal
-- statement:
--   Let $X$ be a nonempty compact metric space and $v:X\to X$ continuous. On $M=X\times X$ let $\theta(x,y)=(y,x)$. Then $\Phi_C(x,y)=(v(x),v(y))$ is continuous and satisfies C-Commutation:
--   $$\theta^2=\mathrm{id},\qquad\Phi_C=\theta\circ\Phi_C\circ\theta.$$
--   For every homeomorphism $f:X\to X$, the map $\Phi_R(x,y)=(f(x),f^{-1}(y))$ is a homeomorphism and satisfies R-Reversal,
--   $$\Phi_R^{-1}=\theta\circ\Phi_R\circ\theta.$$
--   This provides both models and includes genuinely noninvertible commutation examples.
-- source:
--   Fluctuation Theorem and Thermodynamic Formalism, arXiv:1712.05167v3, PDF p. 28, Example 3.4: product constructions for commutation and reversal

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P82

noncomputable section

open Filter MeasureTheory Set

open scoped Topology BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intake100.P82

attribute [local instance] Classical.propDecidable

section CompactDynamics

variable {M : Type*} [instMetric : MetricSpace M] [instCompact : CompactSpace M]
  [instNonempty : Nonempty M] [instMeasurable : MeasurableSpace M] [instBorel : BorelSpace M]

-- Retain standing assumptions even when a displayed lemma does not use them.

include instCompact instNonempty instBorel

local instance : DecidableEq M := Classical.decEq M

/-- Example 3.4, arXiv:1712.05167v3, PDF p.28. Product commutation works
for noninvertible maps; the inverse-coordinate construction uses a homeomorphism. -/
theorem product_symmetries (v : M → M) (hv : Continuous v) :
    (Continuous (fun z : M × M => (v z.1, v z.2)) ∧
      Symmetry (fun z : M × M => (v z.1, v z.2)) (Homeomorph.prodComm M M) false) ∧
    ∀ f : M ≃ₜ M,
      Continuous (fun z : M × M => (f z.1, f.symm z.2)) ∧
      Symmetry (fun z : M × M => (f z.1, f.symm z.2)) (Homeomorph.prodComm M M) true := by sorry

end CompactDynamics

end QAlgorithms.Papers.Independent.Intake100.P82

end
