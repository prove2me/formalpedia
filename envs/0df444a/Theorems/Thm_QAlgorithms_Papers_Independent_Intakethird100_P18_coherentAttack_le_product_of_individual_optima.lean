-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P18_coherentAttack_le_product_of_individual_optima
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P18.coherentAttack_le_product_of_individual_optima
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:28:54.916202+00:00
-- url     : https://prove2.me/theorems/f4f6daa9-13d6-4ca1-98e5-cbe8d51c6215
-- title:
--   Comparison with any product of matching individually optimal attacks
-- statement:
--   Fix $n\ge1$ independent signals in a local prepare-and-measure protocol as above: normalized states, protocol-prescribed independent local choices, separate normalized Bob POVMs, local sifting of positive probability, correct ideal retained decoding, and publicly announced settings without secret symbols. All channel errors are included in Bob's expected disturbance. Eve's attack $C$ has any normalized ancilla, a fixed input-independent joint unitary, and any delayed POVM chosen using only public announcements.
--
--   For each signal $i$, suppose $O_0(i)$ is any physical single-signal attack that is optimal among all such attacks at the exact expected disturbance $D_i(C)$. Let $O_n=\bigotimes_{i=1}^n O_0(i)$, with both independent probes and factorized interactions and measurements. Then
--
--   $$
--   I(C)\le I(O_n),
--   $$
--
--   where $I=H(X\mid B)-H(X\mid B,Y)$ is the total classical Shannon information about the whole raw string after Eve's measurement, in bits, averaged over actual public configurations and outcomes.
--
--   This lemma compares every attack with every matching optimal family; it does not assert that such optimizers exist. The helper labels disclosed in the proof's Game G are not included in the original attack's public data. The statement concerns expected raw-key errors without test acceptance, error correction, privacy amplification, or a final-key security claim.
-- source:
--   On the role of coherent attacks in a type of strategic problem related to quantum key distribution, arXiv:quant-ph/0110089v6, PDF p. 4, Lemma (unnumbered), with context pp.5–6

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P18

noncomputable section

open MeasureTheory

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intakethird100.P18

/-- PDF p.4, separately named Lemma, with proof context on pp.5–6:
every coherent attack is dominated by the product of any individually optimal
single-signal attacks at its matching local disturbances. Optimizer existence
is not assumed as an ambient axiom and is not asserted by this lemma.
The extra labels revealed in Game G are not public data in the original attack. -/
theorem coherentAttack_le_product_of_individual_optima
    (n : ℕ) (hn : 1 ≤ n) (P : Fin n → LocalProtocol)
    (C : Attack P) (A : ProductAttack P)
    (hA : ∀ i, OptimalAt (P i) (qkdDisturbance C i) (A i)) :
    qkdInformation C ≤ productInformation A := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P18

end
