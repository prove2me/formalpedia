-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P11_qutrit_symmetric_dilation_zero_capacity
-- name    : QAlgorithms.Papers.Independent.Support50.P11.qutrit_symmetric_dilation_zero_capacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:11:06.835305+00:00
-- url     : https://prove2.me/theorems/88ccb4eb-78ea-4553-97fa-867f126ee2d4
-- title:
--   §VII (60)–(61): symmetric qutrit dilation and zero unassisted capacity
-- statement:
--   Let $\mathcal W(X)=(\operatorname{Tr}(X)I-X^T)/2$ on a qutrit. In the ordered basis $0,1,2$, define $V_{(j,k),i}=\epsilon_{ijk}/\sqrt2$, with $\epsilon_{012}=1$ and the usual alternating Levi-Civita symbol. Then
--   $$V^\dagger V=I,\qquad\operatorname{Tr}_E(VXV^\dagger)=\mathcal W(X)=\operatorname{Tr}_B(VXV^\dagger)$$
--   for every operator $X$, identifying the environment and output bases. Moreover the channel is antidegradable, in the operational sense that its environment output can be mapped by a CPTP channel to its channel output, and
--   $$Q^{\mathrm{UA}}(\mathcal W)=0.$$
--   This is the paper's concrete symmetric qutrit example with zero unassisted quantum capacity.
-- source:
--   On the power of PPT-preserving and non-signalling codes, arXiv:1406.7142v2, PDF p. 10, §VII (60)–(61): symmetric qutrit dilation and zero unassisted capacity

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

/-- PDF p.10, (60)--(61): the concrete qutrit self-complementary isometry,
antidegradability and zero operational unassisted quantum quantumCodeCapacity. -/
theorem qutrit_symmetric_dilation_zero_capacity :
    wernerIsometryᴴ * wernerIsometry = 1 ∧
    (∀ X : Matrix (Fin 3) (Fin 3) ℂ,
      traceRight (wernerIsometry * X * wernerIsometryᴴ) = wernerHolevoChannel 3 1 X ∧
      traceLeft (wernerIsometry * X * wernerIsometryᴴ) = wernerHolevoChannel 3 1 X) ∧
    HasAntidegradingDilation (wernerHolevoChannel 3 1) ∧ quantumCodeCapacity .UA (wernerHolevoChannel 3 1) = 0 := by sorry

end QAlgorithms.Papers.Independent.Support50.P11

end
