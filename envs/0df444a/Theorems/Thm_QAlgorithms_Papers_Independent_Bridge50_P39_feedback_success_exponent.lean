-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P39_feedback_success_exponent
-- name    : QAlgorithms.Papers.Independent.Bridge50.P39.feedback_success_exponent
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:47:13.736991+00:00
-- url     : https://prove2.me/theorems/bfb85e1a-f247-4f4f-a5c8-60c55836a2f4
-- title:
--   Feedback-assisted sandwiched-Holevo success exponent
-- statement:
--   Let $\mathcal N:A\to B$ be a completely positive trace-preserving map between positive, finite-dimensional complex Hilbert spaces. Let $P$ be any protocol using this same memoryless forward channel $n\ge1$ times to transmit one of $L\ge1$ uniformly distributed messages. The protocol has arbitrary finite local quantum memories, noiseless classical feedback from Bob to Alice, including an initial classical register $X_0$, and a final $L$-outcome POVM. Initially Alice and Bob share no entanglement, and Bob's seed is independent of the message. The encoded conditional states and final output are obtained by executing the protocol's fixed local maps and instruments.
--
--   Suppose either that $\mathcal N$ is entanglement-breaking, with no restriction on the encoding, or that before every use each actual message-and-transcript conditional state is fully separable across Alice's retained memory, the transmitted input and Bob's memory. Write $\rho_m^{\mathrm{final}}$ for Bob's output, including the classical records, and $D_m$ for his decoding effect. For every advertised rate $0\le R\le \log_2 L/n$,
--
--   $$
--   p_{\mathrm{succ}}(P):=\frac1L\sum_{m=1}^L\operatorname{Tr}(D_m\rho_m^{\mathrm{final}})
--   \le 2^{-n E_{\mathrm{sc}}(\mathcal N,R)},\qquad
--   E_{\mathrm{sc}}(\mathcal N,R):=\sup_{\alpha>1}\frac{\alpha-1}{\alpha}\bigl(R-\widetilde\chi_\alpha(\mathcal N)\bigr).
--   $$
--
--   Here $\widetilde\chi_\alpha(\mathcal N)$ is the supremum over all finite mixed-state input ensembles $\{p_x,\rho_x\}$ of $\inf_{\sigma_B}\widetilde D_\alpha(\rho_{XB}\Vert\rho_X\otimes\sigma_B)$, where $\rho_{XB}=\sum_x p_x|x\rangle\langle x|\otimes\mathcal N(\rho_x)$. The comparison $\sigma_B$ ranges over all density operators. The divergence is the support-aware sandwiched divergence in bits. The exponent supremum is extended-real, with $2^{-\infty}=0$.
--
--   This bounds average decoding success at every finite blocklength and supplies the feedback-assisted strong-converse exponent.
-- source:
--   Strong converse exponents for the feedback-assisted classical capacity of entanglement-breaking channels, arXiv:1506.02228v4, PDF p. 11, Theorem 5, (4.29)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P39

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Bridge50.P39

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P09 (relativeD tensorAction)

open QAlgorithms.Papers.Independent.Dependency50.P23 (IsEB ordinaryClassicalCapacity)

open QAlgorithms.Papers.Independent.Information100.P08 (channelHolevo)

open QAlgorithms.Papers.Independent.Information100.P71 (channelPower)

open QAlgorithms.Papers.Independent.Support50.P19
  (channelInformation informationRadius expTwo)

variable {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- PDF p.11, Theorem 5, (4.29), with the rate convention on p.14:
feedback-assisted average success, for EB channels without encoding restrictions,
or for arbitrary channels with branchwise fully separable encoded inputs. -/
theorem feedback_success_exponent [Nonempty A] [Nonempty B]
    (N : Superop A B) (hN : IsChannel N)
    (n L : ℕ) (P : FeedbackCode A B n L) (hP : P.Valid)
    (hclass : IsEB N ∨ P.SeparableInputs N)
    (R : ℝ) (hR : 0 ≤ R) (hRate : R ≤ uniformMessageRate n L) :
    ENNReal.ofReal (P.success N) ≤
      expTwo (-((n : ℝ) : EReal) * strongConverseExponent N R) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P39

end
