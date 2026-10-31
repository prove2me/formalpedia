-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P93_upsilon_tradeoffs
-- name    : QAlgorithms.Papers.Independent.Intake100.P93.upsilon_tradeoffs
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:44:02.339999+00:00
-- url     : https://prove2.me/theorems/8f035d95-137c-4108-8e63-9f05bc8a7e48
-- title:
--   Example 10: Υα tradeoffs and helper-dependent optimum
-- statement:
--   For real $0\le\alpha\le\beta$ with $\alpha^2+\beta^2=1$, let $|\Upsilon_\alpha\rangle=\alpha|0\rangle^A|\Phi^+\rangle^{BC}+\beta|1\rangle^A|\Phi^-\rangle^{BC}$, where $\Phi^\pm=(|00\rangle\pm|11\rangle)/\sqrt2$. Put $h=H_2(\alpha^2)$ and $e=H_2(1/2-\alpha\beta)$. One copy yields one exact Bell pair on $BC$. The asymptotic conclusions include
--
--   $$R_{\rm GHZ}^{\rm LOCC}=h,\qquad (R_{\rm GHZ},R_{\rm EPR}^{BC})=(1-e,e)\quad\text{with helper }A.$$
--
--   With helper $B$ or $C$, the GHZ rate $h$ is achievable. With helper $A$, the largest one-way-broadcast GHZ rate is $1-e$. The computed marginal obeys $E_C(\Upsilon^{BC})=E_F(\Upsilon^{BC})=e$, an evaluation the paper attributes to [34,36]. No reversible transformation is asserted. This example distinguishes helper choice from unrestricted GHZ optimality.
-- source:
--   Entanglement of assistance and multipartite state distillation, arXiv:quant-ph/0505038v1, PDF p. 6, Example 10: Υα tradeoffs and helper-dependent optimum

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P93

namespace QAlgorithms.Papers.Independent.Intake100.P93

open scoped Matrix ComplexConjugate ComplexOrder

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted primitives; no chunk-local aliases.

open Information100.P21 (Op)

open Information100.P08 (PureEnsemble)

open Dependency50.P07 (bipartiteProduct)

open Information100.P67 (receiverChannel)

open Support50.P11 (choiState)

/-- PDF p.6, Example 10: achievable irreversible tradeoffs and the helper-
dependent optimum. The printed incomplete EPR superscript C is corrected to
BC using the sentence immediately before it. Hypothetical reversible Eq.(5)
is not asserted. The cost evaluation is cited by the paper from [34,36]. -/
theorem upsilon_tradeoffs (alpha beta : ℝ) (ha : 0 ≤ alpha) (hab : alpha ≤ beta)
    (hn : alpha^2 + beta^2 = 1) :
    let rho := pureDensity (upsilonVector alpha beta)
    let h := binEntropy2 (alpha^2)
    let e := binEntropy2 (1/2 - alpha*beta)
    DistillationBlock rho .locc 1 2 1 0 1 0 ∧
    AssistedYield rho .locc 0 1 h 0 ∧
    (∀ r : ℝ, AssistedYield rho .locc 0 1 r 0 → r ≤ h) ∧
    AssistedYield rho (.broadcast 1) 0 2 h 0 ∧
    AssistedYield rho (.broadcast 2) 0 1 h 0 ∧
    AssistedYield rho (.broadcast 0) 1 2 (1-e) e ∧
    (∀ r : ℝ, AssistedYield rho (.broadcast 0) 1 2 r 0 ↔ 0 ≤ r ∧ r ≤ 1-e) ∧
    Dependency50.P42.entanglementCost Dependency50.P42.paperBures
      (pairMarginal rho 1 2) = e ∧
    Information100.P08.formation (pairMarginal rho 1 2) = e := by sorry

end

end QAlgorithms.Papers.Independent.Intake100.P93
