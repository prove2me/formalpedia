-- Prove2me | Theorems.Thm_QuantumXoP_Security_lemma_6_9
-- name    : QuantumXoP.Security.lemma_6_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:06:35.381476+00:00
-- url     : https://prove2.me/theorems/7195de1d-b109-4756-8233-77471b8b827d
-- title:
--   Lemma 6.9 — the degree-3 component: $|\langle\mu^{=3}_{XoP[r]},P_A\rangle|=O(q^2/N^r)$
-- statement:
--   Let $n\ge5$, $2\le r\le N/16$, $q\le N/57774$, and let $P_A$ be the representing polynomial of a $q$-query algorithm $A$. Then
--   $$\big|\langle\mu^{=3}_{XoP[r]},P_A\rangle\big|=O\Big(\frac{q^2}{N^r}\Big),$$
--   with a constant depending only on $r$.
--
--   It gives the case $d=3$ of Lemma 6.2, with a stronger bound than needed.
--
--   Differences from the source:
--   - reading: printed without hypotheses; it is one of the four cases of Lemma 6.2 and used only there → the hypotheses of Lemma 6.2: n ≥ 5, 16r ≤ 2^n, 57774q ≤ 2^n, and P_A the acceptance functional of a q-query algorithm; reason: the lemma is the case d of Lemma 6.2 (§6.2–6.5), whose hypotheses are in force (BRIEF pitfall 2)
--   - reading: O(·), the hidden factor depending only on r (abstract; p. 14; p. 34) → ∃ C > 0, quantified after r and before n, q, the workspace, the algorithm and the output map; reason: the paper fixes what the hidden constant may depend on
--   - encoding: a quantum oracle algorithm ends with a binary measurement (Π₀, Π₁ = I − Π₀) of its final state → the published QueryAlg is measured in the computational basis and an arbitrary output map out : (query register × workspace) → Bool gives the output bit; the workspace W and the final unitary U_q are arbitrary; reason: same class of algorithms: every binary projective measurement is a unitary followed by a computational-basis measurement
-- source:
--   Wonseok Choi, Minki Hhan, Junyoung Jang, Quantum Security of XOR of Permutations via Fourier Analysis, STOC 2027 submission #815 (October 2026), p. 28 (PDF p. 30), Lemma 6.9

import Mathlib
import Definitions.Def_QuantumXoP_Security_Advantage

namespace QuantumXoP.Security

open QAlgorithms
open scoped ComplexConjugate

/-- Lemma 6.9 (p. 28): `|⟨μ^{=3}_{XoP[r]}, P_A⟩| = O(q²/N^r)`, under the hypotheses of
Lemma 6.2, the constant depending only on `r`. -/
theorem lemma_6_9 (r : ℕ) (hr : 2 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 5 ≤ n → 16 * r ≤ 2 ^ n → ∀ q : ℕ, 57774 * q ≤ 2 ^ n →
      ∀ (W : Type) [Fintype W] [DecidableEq W] (A : QueryAlg (Qubits n) (Qubits n) W q)
        (out : (Qubits n × Qubits n) × W → Bool),
        ‖innerF (degComp (density (xopLaw n r)) 3) (repPoly A out)‖ ≤
          C * (q : ℝ) ^ 2 / bigN n ^ r := by sorry

end QuantumXoP.Security
