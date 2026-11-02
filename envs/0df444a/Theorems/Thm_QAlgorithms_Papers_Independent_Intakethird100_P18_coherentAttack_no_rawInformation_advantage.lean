-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P18_coherentAttack_no_rawInformation_advantage
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P18.coherentAttack_no_rawInformation_advantage
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:28:30.838742+00:00
-- url     : https://prove2.me/theorems/fcd0a72d-8139-4812-912c-21d70765bfb3
-- title:
--   Coherent attacks give no raw-information advantage at fixed local disturbances
-- statement:
--   Consider a protocol of independently prepared normalized finite-dimensional signals. At each coordinate, Alice independently chooses a secret raw symbol and a local preparation setting according to the prescribed distributions, and Bob independently chooses and performs a local POVM. Local basis reconciliation and sifting retain a positive-probability set of settings; the ideal retained signals decode correctly. Coordinates may have different protocols and distributions. Public announcements contain only the protocol's local settings information, never the secret symbols.
--
--   Let $n\ge1$, and let $d=(d_1,\ldots,d_n)$ be a feasible vector of ensemble-average raw-symbol error probabilities at Bob: some physical attack induces this vector. An attack consists of a fixed normalized ancillary state, a joint unitary independent of the unknown inputs, and an arbitrary final POVM on the retained ancilla, possibly chosen after the public announcements. The ancilla and measurable outcome space are unrestricted. Write $I(C)=H(X\mid B)-H(X\mid B,Y_C)$, in bits, for Eve's total measured Shannon information about the whole raw string $X$, where $B$ is the public announcement and $Y_C$ is her outcome. Both entropies use the actual protocol and outcome probabilities.
--
--   There exist single-signal attacks $O_0(i)$, each maximizing this information among all physical single-signal attacks having disturbance exactly $d_i$, such that their physical product $O_n=\bigotimes_{i=1}^n O_0(i)$ satisfies
--
--   $$
--   D(O_n)=d,\qquad I(O_n)=\sum_{i=1}^n I(O_0(i)),\qquad
--   \forall C\,[D(C)=d\ \Longrightarrow\ I(C)\le I(O_n)].
--   $$
--
--   The optimizing family is chosen at fixed $d$ before the competing attack $C$. Thus the unrestricted coherent optimum is attained by an individual product scheme. This concerns only raw-key information at fixed expected disturbances; no passing-test selection, finite-sample assertion, error correction, privacy amplification, or final-key security conclusion is included.
-- source:
--   On the role of coherent attacks in a type of strategic problem related to quantum key distribution, arXiv:quant-ph/0110089v6, PDF p. 3, Main Theorem; optimizer definition p.4; conclusion p.6

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P18

noncomputable section

open MeasureTheory

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intakethird100.P18

/-- PDF p.3, Main Theorem, optimizer definition on p.4, and concluding formulation
on p.6: at every feasible vector of expected local disturbances, optimized
single-signal attacks exist. Their physical product has exactly that vector,
attains the sum of their raw-information maxima, and dominates every competing
coherent attack at the same vector. The optimizers are chosen before the
competing attack. No test acceptance, EC, PA, or final-key claim is included.
Coordinates are Fin n, i.e. the source's physical signals 1,...,n; the stray
index 0 in the printed entropy sums on pp.5–6 is not an additional signal. -/
theorem coherentAttack_no_rawInformation_advantage
    (n : ℕ) (hn : 1 ≤ n) (P : Fin n → LocalProtocol)
    (d : Fin n → ℝ) (hd : QkdFeasible P d) :
    ∃ A : ProductAttack P,
      (∀ i, OptimalAt (P i) (d i) (A i)) ∧
      productDisturbance A = d ∧
      productInformation A = ∑ i, qkdInformation (A i) ∧
      ∀ C : Attack P, qkdDisturbance C = d → qkdInformation C ≤ productInformation A := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P18

end
