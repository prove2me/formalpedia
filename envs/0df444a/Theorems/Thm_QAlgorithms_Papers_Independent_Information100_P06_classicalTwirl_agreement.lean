-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P06_classicalTwirl_agreement
-- name    : QAlgorithms.Papers.Independent.Information100.P06.classicalTwirl_agreement
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:28:03.960082+00:00
-- url     : https://prove2.me/theorems/6ad466a3-fc5f-4a97-b886-6ca68e664197
-- title:
--   Unnumbered: universally improved twirled classical channels, Eqs.44–46
-- statement:
--   Let d>=2 and n>=2, and let P_i be classical channels on Z_d. Average each channel over simultaneous relabelings by all d! permutations, producing T_cl[P_i]. Set f_i=(1/d) sum_a P_i(a|a). The twirled transition equals f_i on the diagonal and (1-f_i)/(d-1) off the diagonal. Apply the same shared-randomness agreement algorithm to these twirled channels. Its success probability is
--   $$
--   p=\prod_i f_i+\left(\frac1{d-1}\right)^{n-1}\prod_i(1-f_i).
--   $$
--   Whenever p>0, its conditional output Q is a channel and
--   $$
--   F(Q)=\frac{\prod_i f_i}{\prod_i f_i+(1/(d-1))^{n-1}\prod_i(1-f_i)}.
--   $$
--   If 1/d<f_i<1 for every i, then p>0 and F(Q)>f_i>=F(P_i) for every i. This turns the fixed agreement algorithm into a universal classical fidelity-improvement protocol on that domain.
-- source:
--   Universal Improvement of Channel Fidelity via Entanglement Assistance, arXiv:2610.05669v1, PDF p. 7, Unnumbered: universally improved twirled classical channels, Eqs.44–46

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P06

noncomputable section

open scoped Matrix ComplexOrder ENNReal Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Information100.P06

/-- PDF p.7, Eqs.44–46: twirl the actual input channels, then run the same
fixed shared-randomness algorithm. Its success/fidelity formulas hold whenever
success is positive. Strict improvement uses 1/d < f_i < 1, correcting the
printed omission of the upper endpoint: an input of fidelity one cannot
be strictly improved by a channel. -/
theorem classicalTwirl_agreement
    {d n : ℕ} [NeZero d] (hd : 2 ≤ d) (hn : 2 ≤ n)
    (P : Fin n → Transition d) (hP : ∀ i, IsClassicalChannel (P i)) :
    let f := fun i => classicalAverage (P i)
    let T := fun i => classicalTwirl (P i)
    (∀ i, T i = symmetricChannel d (f i)) ∧
    agreementSuccess T = symmetricSuccess (d : ℝ) f ∧
    (0 < symmetricSuccess (d : ℝ) f →
      IsClassicalChannel (agreementOutput T) ∧
      classicalFidelity (agreementOutput T) =
        (∏ i, f i) / symmetricSuccess (d : ℝ) f) ∧
    ((∀ i, 1 / (d : ℝ) < f i ∧ f i < 1) →
      0 < symmetricSuccess (d : ℝ) f ∧
      ∀ i, f i < classicalFidelity (agreementOutput T) ∧
        classicalFidelity (P i) ≤ f i) := by sorry

end QAlgorithms.Papers.Independent.Information100.P06

end
