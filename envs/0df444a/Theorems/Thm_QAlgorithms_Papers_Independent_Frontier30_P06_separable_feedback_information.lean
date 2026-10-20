-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P06_separable_feedback_information
-- name    : QAlgorithms.Papers.Independent.Frontier30.P06.separable_feedback_information
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:25:33.773309+00:00
-- url     : https://prove2.me/theorems/39c814b2-a448-4b37-9632-f222e183956a
-- title:
--   Finite feedback information bound across separable cuts
-- statement:
--   Consider an executed protocol using $n\ge0$ channel blocks $N_0,\ldots,N_{n-1}$, each a positive finite-dimensional completely positive trace-preserving channel. Messages belong to a finite set of size $M\ge1$ and have any probabilities $p_m\ge0$ summing to one. Alice's message-dependent normalized initial states are in product with Bob's normalized message-independent seed. Alice uses trace-preserving encoders and outcome-dependent trace-preserving response maps; Bob uses completely positive instruments with trace-preserving sums. Each block call preserves every retained reference.
--
--   Suppose that at each feedback cut between blocks the actual average state is separable between the message reference together with Bob, and all retained Alice systems, both before and after feedback. Let $B_{\mathrm f}$ contain every system Bob retains at the end, including retained classical records. Let $I_{\mathrm{acc}}(M:B_{\mathrm f})$ optimize the final POVM for this fixed protocol and prior, and let $\chi(N_j)$ maximize output Holevo information over normalized input ensembles to block $j$. Then, in bits,
--
--   $$
--   I_{\mathrm{acc}}(M:B_{\mathrm f})\le I(M:B_{\mathrm f})\le\sum_{j=0}^{n-1}\chi(N_j).
--   $$
--
--   The bound permits message-dependent separable mixture weights and entanglement within each channel block. At zero blocks the information is zero.
-- source:
--   On Feedback and the Classical Capacity of a Noisy Quantum Channel, arXiv:quant-ph/0305176v1, PDF p. 4, III.B

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P06

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology

open Filter

namespace QAlgorithms.Papers.Independent.Frontier30.P06

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P09 (Backward tensorAction)

open QAlgorithms.Papers.Independent.Information100.P08 (channelHolevo)

/-- PDF p.4, III.B: the finite-information extension to actual separable feedback
cuts, with message-dependent mixture weights permitted, rather than merely a
separable average channel-input marginal. -/
theorem separable_feedback_information {ch : ℕ → Backward} {n M : ℕ}
    (P : FeedbackExecution ch n M) (hP : P.Valid) (p : Fin M → ℝ) (hp : Prior p)
    (hsep : P.SeparableCuts p) :
    P.accessible p ≤ P.information p ∧
      P.information p ≤ ∑ j ∈ Finset.range n, channelHolevo (ch j).map := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P06

end
