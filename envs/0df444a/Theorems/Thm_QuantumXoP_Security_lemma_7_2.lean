-- Prove2me | Theorems.Thm_QuantumXoP_Security_lemma_7_2
-- name    : QuantumXoP.Security.lemma_7_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:07:18.280685+00:00
-- url     : https://prove2.me/theorems/c5a9429c-e378-4c8a-abf2-b5f4cb00f755
-- title:
--   Lemma 7.2 — $\mathrm{Adv}_q^{\mathrm{dist}}(D_{PC},D_F)=O(q^{3/2}/N^{3/2})$
-- statement:
--   Let $N=2^n\ge2$. For every integer $q\ge0$,
--   $$\mathrm{Adv}^{\mathrm{dist}}_q(D_{PC},D_F)=O\Big(\frac{q^{3/2}}{N^{3/2}}\Big),$$
--   with an absolute constant.
--
--   It improves Lemma 6.6 when $q^3\ge N$ and yields the middle bound of Theorem 4.1 (Lemma 7.1).
--
--   **Formalization Note** $q^{3/2}$ and $N^{3/2}$ are real powers.
--
--   Differences from the source:
--   - reading: O(·) in a statement that involves no fixed parameter → ∃ C > 0, quantified before every parameter (an absolute constant); reason: the statement has no parameter the constant could depend on
--   - encoding: a quantum oracle algorithm ends with a binary measurement (Π₀, Π₁ = I − Π₀) of its final state → the published QueryAlg is measured in the computational basis and an arbitrary output map out : (query register × workspace) → Bool gives the output bit; the workspace W and the final unitary U_q are arbitrary; reason: same class of algorithms: every binary projective measurement is a unitary followed by a computational-basis measurement
-- source:
--   Wonseok Choi, Minki Hhan, Junyoung Jang, Quantum Security of XOR of Permutations via Fourier Analysis, STOC 2027 submission #815 (October 2026), p. 35 (PDF p. 37), Lemma 7.2

import Mathlib
import Definitions.Def_QuantumXoP_Security_Advantage
import Definitions.Def_QuantumXoP_Security_Planted

namespace QuantumXoP.Security

open QAlgorithms
open scoped ComplexConjugate

/-- Lemma 7.2 (p. 35): for `N = 2^n ≥ 2` and every integer `q ≥ 0`,
`Adv_q^dist(D_PC, D_F) = O(q^{3/2}/N^{3/2})`, with an absolute constant. -/
theorem lemma_7_2 :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (hN : 2 ≤ 2 ^ n) (q : ℕ),
      AdvAtMost (Qubits n) (Qubits n) q (pcLaw n hN) (uniformF n)
        (C * (q : ℝ) ^ ((3 : ℝ) / 2) / bigN n ^ ((3 : ℝ) / 2)) := by sorry

end QuantumXoP.Security
