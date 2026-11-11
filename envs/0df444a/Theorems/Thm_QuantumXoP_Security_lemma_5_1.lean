-- Prove2me | Theorems.Thm_QuantumXoP_Security_lemma_5_1
-- name    : QuantumXoP.Security.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:06:19.938849+00:00
-- url     : https://prove2.me/theorems/85c67668-d50f-489f-9c7f-e9ce08c38b0a
-- title:
--   Lemma 5.1 — $\mathrm{Adv}_q^{\mathrm{dist}}(D_{XoP[r]},D_F)=O(1/N^{r-3/2})$
-- statement:
--   Let $n\ge5$, $2\le r\le N/16$ and $q\le N/57774$. Then
--   $$\mathrm{Adv}^{\mathrm{dist}}_q(D_{XoP[r]},D_F)=O\Big(\frac1{N^{r-1.5}}\Big),$$
--   with a constant depending only on $r$.
--
--   This is the third bound of Theorem 4.1, a uniform upper bound for all query counts in the stated range.
--
--   **Formalization Note** $N^{r-3/2}$ is a real power.
--
--   Differences from the source:
--   - reading: r ≤ N/16 without 2 ≤ r → 2 ≤ r; reason: the standing assumption of the section (p. 14 for §5; "As in Theorem 4.1", p. 34, for §7) supplies 2 ≤ r
--   - reading: O(·), the hidden factor depending only on r (abstract; p. 14; p. 34) → ∃ C > 0, quantified after r and before n, q, the workspace, the algorithm and the output map; reason: the paper fixes what the hidden constant may depend on
--   - encoding: a quantum oracle algorithm ends with a binary measurement (Π₀, Π₁ = I − Π₀) of its final state → the published QueryAlg is measured in the computational basis and an arbitrary output map out : (query register × workspace) → Bool gives the output bit; the workspace W and the final unitary U_q are arbitrary; reason: same class of algorithms: every binary projective measurement is a unitary followed by a computational-basis measurement
-- source:
--   Wonseok Choi, Minki Hhan, Junyoung Jang, Quantum Security of XOR of Permutations via Fourier Analysis, STOC 2027 submission #815 (October 2026), p. 14 (PDF p. 16), Lemma 5.1, with the §5 standing assumption (p. 14)

import Mathlib
import Definitions.Def_QuantumXoP_Security_Advantage

namespace QuantumXoP.Security

open QAlgorithms
open scoped ComplexConjugate

/-- Lemma 5.1 (p. 14): if `n ≥ 5`, `2 ≤ r ≤ N/16` and `q ≤ N/57774`, then
`Adv_q^dist(D_{XoP[r]}, D_F) = O(1/N^{r−1.5})`, the constant depending only on `r`. -/
theorem lemma_5_1 (r : ℕ) (hr : 2 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 5 ≤ n → 16 * r ≤ 2 ^ n → ∀ q : ℕ, 57774 * q ≤ 2 ^ n →
      AdvAtMost (Qubits n) (Qubits n) q (xopLaw n r) (uniformF n)
        (C / bigN n ^ ((r : ℝ) - 3 / 2)) := by sorry

end QuantumXoP.Security
