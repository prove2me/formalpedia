-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P11_werner_ppt_capacities
-- name    : QAlgorithms.Papers.Independent.Support50.P11.werner_ppt_capacities
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:12:49.246935+00:00
-- url     : https://prove2.me/theorems/4f0d2d36-053a-4435-b8d7-113e3ede1806
-- title:
--   §VII (63): PPTp and zero-error capacities of Werner–Holevo channels
-- statement:
--   For every integer $d\ge2$, let $\mathcal W^{(d,1)}(X)=(\operatorname{Tr}(X)I-X^T)/(d-1)$ be the Werner–Holevo channel. Its operational vanishing-error and zero-error quantum capacities under forward-assisted PPT-preserving codes satisfy
--   $$Q^{\mathrm{PPTp}}(\mathcal W^{(d,1)})=Q_0^{\mathrm{PPTp}}(\mathcal W^{(d,1)})=\log_2\frac{d+2}{d}.$$
--   The zero-error capacity takes the supremum of exact finite-block rates over all positive block lengths and code dimensions. This states the channel corollary of the cited distillation result, with logarithms in bits.
-- source:
--   On the power of PPT-preserving and non-signalling codes, arXiv:1406.7142v2, PDF p. 11, §VII (63): PPTp and zero-error capacities of Werner–Holevo channels

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

/-- PDF p.11, (63): both PPTp capacities equal log2((d+2)/d).
At d=3 this is log2(5/3); the later 5/2 prose is not used. -/
theorem werner_ppt_capacities
    (d : ℕ) (hd : 2 ≤ d) :
    quantumCodeCapacity .PPTp (wernerHolevoChannel d 1) =
      ENNReal.ofReal (Real.log (((d : ℝ) + 2) / d) / Real.log 2) ∧
    zeroErrorCodeCapacity .PPTp (wernerHolevoChannel d 1) =
      ENNReal.ofReal (Real.log (((d : ℝ) + 2) / d) / Real.log 2) := by sorry

end QAlgorithms.Papers.Independent.Support50.P11

end
