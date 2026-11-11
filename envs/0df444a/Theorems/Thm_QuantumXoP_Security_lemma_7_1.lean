-- Prove2me | Theorems.Thm_QuantumXoP_Security_lemma_7_1
-- name    : QuantumXoP.Security.lemma_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:07:23.376063+00:00
-- url     : https://prove2.me/theorems/f0c2325f-ce9a-4c77-84c0-7389d07ec775
-- title:
--   Lemma 7.1 — $\mathrm{Adv}_q^{\mathrm{dist}}(D_{XoP[r]},D_F)=O(q^{3/2}/N^{r-1/2})$
-- statement:
--   Let $n\ge5$, $2\le r\le N/16$ and $q\le N/57774$. Then
--   $$\mathrm{Adv}^{\mathrm{dist}}_q(D_{XoP[r]},D_F)=O\Big(\frac{q^{3/2}}{N^{r-1/2}}\Big),$$
--   with a constant depending only on $r$.
--
--   This is the second bound of Theorem 4.1, whose rate is smallest among the three branches when $N^{1/3}\le q\le N^{2/3}$, within the stated query range.
--
--   **Formalization Note** The powers are real powers.
--
--   Differences from the source:
--   - reading: r ≤ N/16 without 2 ≤ r → 2 ≤ r; reason: the standing assumption of the section (p. 14 for §5; "As in Theorem 4.1", p. 34, for §7) supplies 2 ≤ r
--   - reading: O(·), the hidden factor depending only on r (abstract; p. 14; p. 34) → ∃ C > 0, quantified after r and before n, q, the workspace, the algorithm and the output map; reason: the paper fixes what the hidden constant may depend on
--   - encoding: a quantum oracle algorithm ends with a binary measurement (Π₀, Π₁ = I − Π₀) of its final state → the published QueryAlg is measured in the computational basis and an arbitrary output map out : (query register × workspace) → Bool gives the output bit; the workspace W and the final unitary U_q are arbitrary; reason: same class of algorithms: every binary projective measurement is a unitary followed by a computational-basis measurement
-- source:
--   Wonseok Choi, Minki Hhan, Junyoung Jang, Quantum Security of XOR of Permutations via Fourier Analysis, STOC 2027 submission #815 (October 2026), p. 34 (PDF p. 36), Lemma 7.1

import Mathlib
import Definitions.Def_QuantumXoP_Security_Advantage

namespace QuantumXoP.Security

open QAlgorithms
open scoped ComplexConjugate

/-- Lemma 7.1 (p. 34): if `n ≥ 5`, `2 ≤ r ≤ N/16` and `q ≤ N/57774`, then
`Adv_q^dist(D_{XoP[r]}, D_F) = O(q^{3/2}/N^{r−1/2})`, the constant depending only on `r`. -/
theorem lemma_7_1 (r : ℕ) (hr : 2 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 5 ≤ n → 16 * r ≤ 2 ^ n → ∀ q : ℕ, 57774 * q ≤ 2 ^ n →
      AdvAtMost (Qubits n) (Qubits n) q (xopLaw n r) (uniformF n)
        (C * (q : ℝ) ^ ((3 : ℝ) / 2) / bigN n ^ ((r : ℝ) - 1 / 2)) := by sorry

end QuantumXoP.Security
