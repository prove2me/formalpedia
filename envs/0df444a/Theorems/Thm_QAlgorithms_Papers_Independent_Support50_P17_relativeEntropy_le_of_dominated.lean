-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P17_relativeEntropy_le_of_dominated
-- name    : QAlgorithms.Papers.Independent.Support50.P17.relativeEntropy_le_of_dominated
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-29T18:22:06.628339+00:00
-- url     : https://prove2.me/theorems/f2a7d687-2c50-4135-9f33-a470502ecf93
-- title:
--   Relative entropy increases when the first argument is enlarged above the reference
-- statement:
--   Let $\rho\ge0$ and $\sigma>0$ (positive definite) be operators on a finite-dimensional complex Hilbert space, and let $W$ be an operator with $W\ge\rho$ and $W\ge\sigma$ in the Loewner order. Then, for the unnormalised Umegaki relative entropy $D(A\|B)=\operatorname{Tr}A\log A-\operatorname{Tr}A\log B$ (with $0\log0=0$),
--
--   $$
--   D(\rho\|\sigma)\le D(W\|\sigma).
--   $$
--
--   The statement follows from the operator monotonicity of the logarithm, and lets one replace a state by a larger, structurally simpler operator when bounding relative entropies.
--
--   **Formalization Note** `relativeEntropy` is the frozen definition of Dependency50.P21; the order hypotheses are stated as positive semidefiniteness of $W-\rho$ and $W-\sigma$.
-- source:
--   Operator monotonicity of log (Loewner; Bhatia, Matrix Analysis, Exercise V.1.10 / Theorem V.1.9); used in Audenaert--Eisert, Continuity bounds on the quantum relative entropy - II, arXiv:1105.2656v3, proof of Corollary 1 (PDF p. 9), case T >= beta

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P17

noncomputable section

open MeasureTheory

open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

open QAlgorithms.Papers.Independent.Dependency50.P21 (IsSupported relativeEntropy)

namespace QAlgorithms.Papers.Independent.Support50.P17

attribute [local instance] Classical.propDecidable Classical.decEq

theorem relativeEntropy_le_of_dominated {I : Type*} [Fintype I] [DecidableEq I]
    (rho sigma W : Matrix I I ℂ) (hrho : rho.PosSemidef) (hsigma : sigma.PosDef)
    (hWrho : (W - rho).PosSemidef) (hWsigma : (W - sigma).PosSemidef) :
    relativeEntropy rho sigma ≤ relativeEntropy W sigma := by sorry

end QAlgorithms.Papers.Independent.Support50.P17

end
