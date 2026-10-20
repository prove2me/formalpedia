-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P09_bicovariant_regularized_bound
-- name    : QAlgorithms.Papers.Independent.Dependency50.P09.bicovariant_regularized_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:16:58.996206+00:00
-- url     : https://prove2.me/theorems/f5c4c63e-a870-4780-b98e-399d223ba564
-- title:
--   Unnumbered regularized-to-single-letter Upsilon bound (329)
-- statement:
--   Let $N$ be a bipartite channel covariant under two independent input unitary one-designs and matching unitary output representations. For $\alpha>1$, define regularized Upsilon by first regularizing the divergence for each one-use CP comparison and then minimizing over $\beta\le1$.
--
--   $$
--   \widetilde\Upsilon_\alpha^{\rm reg}(N)\le\widetilde\Upsilon_\alpha(N).
--   $$
--
--   This is a structural property of the paper's forward communication measures.
--
--   **Formalization Note** Only an inequality is claimed, not equality or additivity. Sandwiched exponent corrected as documented.
-- source:
--   Bounding the forward classical capacity of bipartite quantum channels, arXiv:2010.01058v3, PDF p. 18, Unnumbered regularized-to-single-letter Upsilon bound (329)

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

/-- Unnumbered regularized-to-single-letter Upsilon bound (329), arXiv:2010.01058v3, PDF pp.18.
Only an inequality is claimed, not equality or additivity. Sandwiched exponent corrected as documented.
Source correction: Printed: (149)-(150) print the sandwiched exponent -(1-alpha)/(2 alpha). Changed: Use (1-alpha)/(2 alpha). Why: At rho=sigma=I/d the printed exponent gives -2 log2 d, contradicting normalization (144) and limit (152). -/
theorem bicovariant_regularized_bound {A : Type} [Fintype A] [Nonempty A]
    {B : Type} [Fintype B] [Nonempty B]
    {C : Type} [Fintype C] [Nonempty C]
    {D : Type} [Fintype D] [Nonempty D]
    (N : Superop (A × B) (C × D)) (hN : IsChannel N)
    (hcov : HasBiDesign N) (alpha : ℝ) (halpha : 1 < alpha) :
    upsilonReg (sandwichedD alpha) N ≤ upsilon (sandwichedD alpha) N := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P09

end
