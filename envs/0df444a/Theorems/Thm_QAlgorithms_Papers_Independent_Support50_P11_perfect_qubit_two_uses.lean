-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P11_perfect_qubit_two_uses
-- name    : QAlgorithms.Papers.Independent.Support50.P11.perfect_qubit_two_uses
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:15:14.202594+00:00
-- url     : https://prove2.me/theorems/e063b2ab-4614-47bd-8cf2-0ed0c167cb8f
-- title:
--   Example 9: one qubit perfectly in two uses with NS and PPTp
-- statement:
--   Let $\mathcal N=(\mathcal W^{(3,1)})^{\otimes2}$, with input $A'_1A'_2$ and output $B_1B_2$, and put $\rho=I_{A'}/9$. Let $S,A$ be the symmetric and antisymmetric projectors for one input–output pair. Set
--   $$\Lambda=\frac19\left[\frac3{32}S\otimes S+\frac7{32}(S\otimes A+A\otimes S)+A\otimes A\right],\qquad
--   \Gamma=\frac{\rho\otimes I_B-\Lambda}{3}.$$
--   The actual bipartite code reconstructed from (29), with $K=2$, is CPTP, non-signalling in both directions and PPT-preserving. Its average input is $\rho$ and
--   $$F(\mathcal N\text{ linked with this code})=\operatorname{Re}\operatorname{Tr}(N^T\Lambda)=1.$$
--   The pair $(\rho,\Lambda)$ satisfies every selected primal constraint. The common factor $1/9$, omitted in print, is necessary for the operational perfect-transmission example.
-- source:
--   On the power of PPT-preserving and non-signalling codes, arXiv:1406.7142v2, PDF p. 12, Example 9: one qubit perfectly in two uses with NS and PPTp

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P11

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Support50.P11

open QAlgorithms.Papers.Independent.Information100.P34 (choi dephasing permutationMatrix)

open QAlgorithms.Papers.Independent.Information100.P21 (pt)

open QAlgorithms.Papers.Independent.Dependency50.P09 (tensorAction)

open QAlgorithms.Papers.Independent.Information100.P76 (swapMatrix)

open QAlgorithms.Papers.Independent.Information100.P69 (replacer)

open QAlgorithms.Papers.Independent.Gap20.P19 (wernerIsometry)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF p.12, Example 9: the explicit perfect two-use qubit code.
The printed Lambda lacks a common 1/9; it is corrected here to satisfy (32),(34),(35).
Gamma is (rho tensor I-Lambda)/3 through reconstructedCode. -/
theorem perfect_qubit_two_uses :
    let N := piSuperop (fun _ : Fin 2 => wernerHolevoChannel 3 1)
    let rho : Matrix (Fin 2 → Fin 3) (Fin 2 → Fin 3) ℂ := (9 : ℂ)⁻¹ • 1
    let Z := reconstructedCode 2 (by decide) rho exampleLambda
    Primal 2 true true rho exampleLambda ∧ primalObjective N exampleLambda = 1 ∧
    IsForwardCode 2 .both Z ∧ codeAverageInput 2 Z = rho ∧ channelFidelity 2 (link 2 N Z) = 1 := by sorry

end QAlgorithms.Papers.Independent.Support50.P11

end
