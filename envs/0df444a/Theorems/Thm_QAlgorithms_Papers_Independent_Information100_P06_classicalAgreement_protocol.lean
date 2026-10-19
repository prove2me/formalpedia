-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P06_classicalAgreement_protocol
-- name    : QAlgorithms.Papers.Independent.Information100.P06.classicalAgreement_protocol
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:26:51.657895+00:00
-- url     : https://prove2.me/theorems/5578509a-369c-49d9-998f-751dec2bf356
-- title:
--   Unnumbered: shared-randomness protocol and identity-biased improvement
-- statement:
--   Let d>=2 and n>=2. Each P_i(b|a) is a classical channel on the cyclic alphabet Z_d: its probabilities are nonnegative and sum to one over b for every a. Share a uniform r in Z_d. On message k, send a=r-k through each of the n channels. Accept exactly when all received symbols equal one b and output r-b. Thus the unnormalized successful transition is
--   $$
--   B(j|k)=\frac1d\sum_{a,b}\mathbf1_{\{j=k+a-b\}}\prod_iP_i(b|a).
--   $$
--   Its input-independent success probability satisfies
--   $$
--   p=\frac1d\sum_{a,b}\prod_iP_i(b|a)\in[0,1].
--   $$
--   If p>0, Q=B/p is a channel and its classical fidelity, F(Q)=min_k Q(k|k), is
--   $$
--   F(Q)=\frac{\sum_a\prod_iP_i(a|a)}{\sum_{a,b}\prod_iP_i(b|a)}.
--   $$
--   If every input is identity-biased, meaning P_i(a|a)>P_i(b|a) whenever b!=a, and F(P_i)<1 for every i, then p>0 and F(Q)>F(P_i) for all i. This is the explicit shared-randomness protocol, using no communication beyond the given channels.
-- source:
--   Universal Improvement of Channel Fidelity via Entanglement Assistance, arXiv:2610.05669v1, PDF p. 6, Unnumbered: shared-randomness protocol and identity-biased improvement

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P06

noncomputable section

open scoped Matrix ComplexOrder ENNReal Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Information100.P06

/-- PDF p.6, Eqs.37–43: the explicit shared-randomness agreement protocol,
including n-input output and success formulas and strict improvement for
nonperfect identity-biased inputs. The nonperfect guard corrects the printed
strict comparison at perfect-channel endpoints: a perfect input has fidelity
one, which no output channel can strictly exceed. -/
theorem classicalAgreement_protocol
    {d n : ℕ} [NeZero d] (hd : 2 ≤ d) (hn : 2 ≤ n)
    (P : Fin n → Transition d) (hP : ∀ i, IsClassicalChannel (P i)) :
    (∀ k, ∑ j, agreementBranch P j k = agreementSuccess P) ∧
    0 ≤ agreementSuccess P ∧ agreementSuccess P ≤ 1 ∧
    (0 < agreementSuccess P →
      IsClassicalChannel (agreementOutput P) ∧
      classicalFidelity (agreementOutput P) =
        (∑ a, ∏ i, P i a a) / (∑ a, ∑ b, ∏ i, P i b a)) ∧
    ((∀ i, IdentityBiased (P i) ∧ classicalFidelity (P i) < 1) →
      0 < agreementSuccess P ∧
      ∀ i, classicalFidelity (P i) < classicalFidelity (agreementOutput P)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P06

end
