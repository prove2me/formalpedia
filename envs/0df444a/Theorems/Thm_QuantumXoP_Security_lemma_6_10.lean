-- Prove2me | Theorems.Thm_QuantumXoP_Security_lemma_6_10
-- name    : QuantumXoP.Security.lemma_6_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:06:57.519565+00:00
-- url     : https://prove2.me/theorems/c330e6cb-1209-4e31-9d8b-12f792f302af
-- title:
--   Lemma 6.10 — several planted collisions: $\mathrm{Adv}_q^{\mathrm{dist}}(D_{PC,k},D_F)=O(q^3/N^2)$ for $k=2,3$
-- statement:
--   For $k\in\{2,3\}$, every $n$ with $N\ge2k$ and every $q$,
--   $$\mathrm{Adv}^{\mathrm{dist}}_q(D_{PC,k},D_F)=O\Big(\frac{q^3}{N^2}\Big),$$
--   with an absolute constant.
--
--   It is used for the degree-4 and degree-6 components (Lemmas 6.12 and 6.14).
--
--   Differences from the source:
--   - encoding: no condition on n is printed → 2^n ≥ 2k; reason: D_{PC,k} samples 2k distinct inputs and is undefined for smaller N; the hypothesis only excludes undefined cases
--   - reading: O(·) in a statement that involves no fixed parameter → ∃ C > 0, quantified before every parameter (an absolute constant); reason: the statement has no parameter the constant could depend on
--   - encoding: a quantum oracle algorithm ends with a binary measurement (Π₀, Π₁ = I − Π₀) of its final state → the published QueryAlg is measured in the computational basis and an arbitrary output map out : (query register × workspace) → Bool gives the output bit; the workspace W and the final unitary U_q are arbitrary; reason: same class of algorithms: every binary projective measurement is a unitary followed by a computational-basis measurement
-- source:
--   Wonseok Choi, Minki Hhan, Junyoung Jang, Quantum Security of XOR of Permutations via Fourier Analysis, STOC 2027 submission #815 (October 2026), p. 30 (PDF p. 32), Lemma 6.10 (proof App. B.1, pp. 42–43)

import Mathlib
import Definitions.Def_QuantumXoP_Security_Advantage
import Definitions.Def_QuantumXoP_Security_Planted

namespace QuantumXoP.Security

open QAlgorithms
open scoped ComplexConjugate

/-- Lemma 6.10 (p. 30): `Adv_q^dist(D_{PC,k}, D_F) = O(q³/N²)` for `k = 2, 3`, with an absolute
constant. -/
theorem lemma_6_10 :
    ∃ C : ℝ, 0 < C ∧ ∀ (n k : ℕ), (k = 2 ∨ k = 3) → ∀ (hN : 2 * k ≤ 2 ^ n) (q : ℕ),
      AdvAtMost (Qubits n) (Qubits n) q (pcKLaw n k hN) (uniformF n)
        (C * (q : ℝ) ^ 3 / bigN n ^ 2) := by sorry

end QuantumXoP.Security
