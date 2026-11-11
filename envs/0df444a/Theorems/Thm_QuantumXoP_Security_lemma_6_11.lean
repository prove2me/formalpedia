-- Prove2me | Theorems.Thm_QuantumXoP_Security_lemma_6_11
-- name    : QuantumXoP.Security.lemma_6_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:06:35.952387+00:00
-- url     : https://prove2.me/theorems/c1507468-5334-4337-8a83-8002754fdeaa
-- title:
--   Lemma 6.11 — planted 4-XOR: $\mathrm{Adv}_q^{\mathrm{dist}}(D_{4X},D_F)=O(q^3/N^2)$
-- statement:
--   For every $n$ with $N\ge4$ and every $q$,
--   $$\mathrm{Adv}^{\mathrm{dist}}_q(D_{4X},D_F)=O\Big(\frac{q^3}{N^2}\Big),$$
--   with an absolute constant.
--
--   It is used for the degree-4 component (Lemma 6.12).
--
--   Differences from the source:
--   - encoding: no condition on n is printed → 2^n ≥ 4; reason: D_4X samples 4 distinct inputs and is undefined for smaller N; the hypothesis only excludes undefined cases
--   - reading: O(·) in a statement that involves no fixed parameter → ∃ C > 0, quantified before every parameter (an absolute constant); reason: the statement has no parameter the constant could depend on
--   - encoding: a quantum oracle algorithm ends with a binary measurement (Π₀, Π₁ = I − Π₀) of its final state → the published QueryAlg is measured in the computational basis and an arbitrary output map out : (query register × workspace) → Bool gives the output bit; the workspace W and the final unitary U_q are arbitrary; reason: same class of algorithms: every binary projective measurement is a unitary followed by a computational-basis measurement
-- source:
--   Wonseok Choi, Minki Hhan, Junyoung Jang, Quantum Security of XOR of Permutations via Fourier Analysis, STOC 2027 submission #815 (October 2026), p. 30 (PDF p. 32), Lemma 6.11 (proof App. B.3, pp. 44–45)

import Mathlib
import Definitions.Def_QuantumXoP_Security_Advantage
import Definitions.Def_QuantumXoP_Security_Planted

namespace QuantumXoP.Security

open QAlgorithms
open scoped ComplexConjugate

/-- Lemma 6.11 (p. 30): `Adv_q^dist(D_4X, D_F) = O(q³/N²)`, with an absolute constant. -/
theorem lemma_6_11 :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (hN : 4 ≤ 2 ^ n) (q : ℕ),
      AdvAtMost (Qubits n) (Qubits n) q (x4Law n hN) (uniformF n)
        (C * (q : ℝ) ^ 3 / bigN n ^ 2) := by sorry

end QuantumXoP.Security
