-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P11_werner_nonSignalling_entanglement_capacities
-- name    : QAlgorithms.Papers.Independent.Support50.P11.werner_nonSignalling_entanglement_capacities
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:13:36.083986+00:00
-- url     : https://prove2.me/theorems/973b3909-6cdd-42e5-b867-3de7d666f7ab
-- title:
--   §VII (64): NS and EA capacities of Werner–Holevo channels
-- statement:
--   For every integer $d\ge2$, let $\mathcal W^{(d,1)}(X)=(\operatorname{Tr}(X)I-X^T)/(d-1)$. The operational NS and entanglement-assisted quantum capacities of its memoryless channel are
--   $$Q^{\mathrm{NS}}(\mathcal W^{(d,1)})=Q^{\mathrm{EA}}(\mathcal W^{(d,1)})=\frac12\log_2\frac{2d}{d-1}.$$
--   These capacities use normalized entanglement fidelity, parallel tensor powers and vanishing error. The formula concerns the antisymmetric endpoint $\alpha=1$ and includes $d=2$.
-- source:
--   On the power of PPT-preserving and non-signalling codes, arXiv:1406.7142v2, PDF p. 11, §VII (64): NS and EA capacities of Werner–Holevo channels

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

/-- PDF p.11, (64): NS and EA capacities of the antisymmetric endpoint channel. -/
theorem werner_nonSignalling_entanglement_capacities
    (d : ℕ) (hd : 2 ≤ d) :
    quantumCodeCapacity .NS (wernerHolevoChannel d 1) =
      ENNReal.ofReal ((Real.log (2 * (d : ℝ) / ((d : ℝ) - 1)) / Real.log 2) / 2) ∧
    quantumCodeCapacity .EA (wernerHolevoChannel d 1) =
      ENNReal.ofReal ((Real.log (2 * (d : ℝ) / ((d : ℝ) - 1)) / Real.log 2) / 2) := by sorry

end QAlgorithms.Papers.Independent.Support50.P11

end
