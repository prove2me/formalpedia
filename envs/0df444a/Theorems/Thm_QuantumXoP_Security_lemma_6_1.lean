-- Prove2me | Theorems.Thm_QuantumXoP_Security_lemma_6_1
-- name    : QuantumXoP.Security.lemma_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:07:07.715518+00:00
-- url     : https://prove2.me/theorems/03715b6b-15fb-456b-a3cb-399d1f220db6
-- title:
--   Lemma 6.1 — $\mathrm{Adv}_q^{\mathrm{dist}}(D_{XoP[r]},D_F)=O(q^3/N^r)$
-- statement:
--   Let $n\ge5$, $2\le r\le N/16$ and $q\le N/57774$. Then
--   $$\mathrm{Adv}^{\mathrm{dist}}_q(D_{XoP[r]},D_F)=O\Big(\frac{q^3}{N^r}\Big),$$
--   with a constant depending only on $r$.
--
--   This is the first bound of Theorem 4.1, the strongest for few queries.
--
--   Differences from the source:
--   - reading: O(·), the hidden factor depending only on r (abstract; p. 14; p. 34) → ∃ C > 0, quantified after r and before n, q, the workspace, the algorithm and the output map; reason: the paper fixes what the hidden constant may depend on
--   - encoding: a quantum oracle algorithm ends with a binary measurement (Π₀, Π₁ = I − Π₀) of its final state → the published QueryAlg is measured in the computational basis and an arbitrary output map out : (query register × workspace) → Bool gives the output bit; the workspace W and the final unitary U_q are arbitrary; reason: same class of algorithms: every binary projective measurement is a unitary followed by a computational-basis measurement
-- source:
--   Wonseok Choi, Minki Hhan, Junyoung Jang, Quantum Security of XOR of Permutations via Fourier Analysis, STOC 2027 submission #815 (October 2026), p. 25 (PDF p. 27), Lemma 6.1

import Mathlib
import Definitions.Def_QuantumXoP_Security_Advantage

namespace QuantumXoP.Security

open QAlgorithms
open scoped ComplexConjugate

/-- Lemma 6.1 (p. 25): if `n ≥ 5`, `2 ≤ r ≤ N/16` and `q ≤ N/57774`, then
`Adv_q^dist(D_{XoP[r]}, D_F) = O(q³/N^r)`, the constant depending only on `r`. -/
theorem lemma_6_1 (r : ℕ) (hr : 2 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 5 ≤ n → 16 * r ≤ 2 ^ n → ∀ q : ℕ, 57774 * q ≤ 2 ^ n →
      AdvAtMost (Qubits n) (Qubits n) q (xopLaw n r) (uniformF n)
        (C * (q : ℝ) ^ 3 / bigN n ^ r) := by sorry

end QuantumXoP.Security
