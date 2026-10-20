-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P09_petz_sandwiched_lowerSemicontinuous
-- name    : QAlgorithms.Papers.Independent.Dependency50.P09.petz_sandwiched_lowerSemicontinuous
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:14:10.193469+00:00
-- url     : https://prove2.me/theorems/e151d920-1fa9-49cb-9b26-a969ed532f2a
-- title:
--   Remark 38 (fully specified Petz and sandwiched extension)
-- statement:
--   Fix positive-dimensional finite ports and $\alpha>0$, $\alpha\ne1$. Give the domain of CPTP/CP pairs $(N,M)$ its finite-dimensional coefficient topology. Channel divergences use all finite references and normalized joint inputs, even below the DPI ranges.
--
--   $$
--   (N,M)\longmapsto D_\alpha(N\Vert M),\qquad (N,M)\longmapsto\widetilde D_\alpha(N\Vert M)\quad\text{are jointly lower semicontinuous}.
--   $$
--
--   This is a structural property of the paper's forward communication measures.
--
--   **Formalization Note** Only the fully specified Petz/sandwiched extension is stated; the unrestricted geometric final sentence is separately deferred. Sandwiched exponent corrected as documented.
-- source:
--   Bounding the forward classical capacity of bipartite quantum channels, arXiv:2010.01058v3, PDF p. 28, Remark 38 (fully specified Petz and sandwiched extension)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P09

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology Matrix.Norms.Elementwise

open Filter

namespace QAlgorithms.Papers.Independent.Dependency50.P09

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P69 (CP)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Information100.P06 (traceOutput)

open QAlgorithms.Papers.Independent.Information100.P58 (testingD singleErasure)

open QAlgorithms.Papers.Independent.Information100.P08 (depolarizing)

open QAlgorithms.Papers.Independent.Information100.P04 (werner)

/-- Remark 38 (fully specified Petz and sandwiched extension), arXiv:2010.01058v3, PDF pp.28.
Only the fully specified Petz/sandwiched extension is stated; the unrestricted geometric final sentence is separately deferred. Sandwiched exponent corrected as documented.
Source correction: Printed: (149)-(150) print the sandwiched exponent -(1-alpha)/(2 alpha). Changed: Use (1-alpha)/(2 alpha). Why: At rho=sigma=I/d the printed exponent gives -2 log2 d, contradicting normalization (144) and limit (152). -/
theorem petz_sandwiched_lowerSemicontinuous {I : Type} [Fintype I] [Nonempty I]
    {J : Type} [Fintype J] [Nonempty J]
    (alpha : ℝ) (halpha : 0 < alpha ∧ alpha ≠ 1) :
    LowerSemicontinuous (pairD (I := I) (J := J) (petzD alpha)) ∧
      LowerSemicontinuous (pairD (I := I) (J := J) (sandwichedD alpha)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P09

end
