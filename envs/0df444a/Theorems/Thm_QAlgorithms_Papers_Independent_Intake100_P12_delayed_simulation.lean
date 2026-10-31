-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P12_delayed_simulation
-- name    : QAlgorithms.Papers.Independent.Intake100.P12.delayed_simulation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:05:11.477606+00:00
-- url     : https://prove2.me/theorems/c9c05007-3e02-4e19-b473-139f85a4efc8
-- title:
--   A uniformly scaled delayed parallel simulation
-- statement:
--   Let all physical wire dimensions be positive. Let $(S,F)$ be a general two-branch superinstrument, including possibly indefinite causal order, and put
--
--   $$d_{\rm total}=\prod_{i=0}^{k}d_{I_i}\prod_{i=0}^{k}d_{O_i}.$$
--
--   There is a delayed parallel instrument with success Choi matrix $S_P=S/d_{\rm total}$ and a positive complementary failure branch. For every combined oracle Choi matrix $J$,
--
--   $$\mathcal L_{S_P}(J)=\frac{1}{d_{\rm total}}\mathcal L_S(J).$$
--
--   In particular, if $S$ implements a unitary target with probability $p_U$, the same simulator implements it with probability $p_U/d_{\rm total}$ for every $U$, even when $p_U$ depends on $U$. With all wires of dimension $d$, $d_{\rm total}=d^{2k+2}$.
--
--   This states the explicit scaled map from the source proof, not equality with the unscaled operation.
-- source:
--   Probabilistic exact universal quantum circuits for transforming unitary operations, arXiv:1909.01366v2, PDF p. 10, Lemma 1

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P12

noncomputable section

open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder Kronecker

namespace QAlgorithms.Papers.Independent.Intake100.P12

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Dependency50.P26 (ChannelChoi)

/-- PDF p.10, Lemma 1 and its explicit proof: the same simulator realizes S/dtotal
on every input map, hence p_U/dtotal for every unitary task even when p_U varies.
The identity completion retains the failure branch. This does not assert realization
of the unscaled supermap. -/
theorem delayed_simulation {k : ℕ} (w : OracleWireDimensions k) (hw : PositiveWires w)
    (S F : Op (ProcessBasis w)) (hS : S.PosSemidef) (hF : F.PosSemidef)
    (hC : GeneralDeterministic w (S+F)) :
    ∃ FP : Op (ProcessBasis w),
      DelayedInstrument w (((totalDimension w : ℂ)⁻¹) • S) FP ∧
      ∀ J, evaluateOracleSlots (((totalDimension w : ℂ)⁻¹) • S) J =
        ((totalDimension w : ℂ)⁻¹) • evaluateOracleSlots S J := by sorry

end QAlgorithms.Papers.Independent.Intake100.P12

end
