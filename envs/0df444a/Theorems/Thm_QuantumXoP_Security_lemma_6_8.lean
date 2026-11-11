-- Prove2me | Theorems.Thm_QuantumXoP_Security_lemma_6_8
-- name    : QuantumXoP.Security.lemma_6_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:06:47.996032+00:00
-- url     : https://prove2.me/theorems/99e43236-c9c4-4383-ac85-5c6e10cb35f9
-- title:
--   Lemma 6.8 — $\mathrm{Adv}_q^{\mathrm{dist}}(D_{3PC},D_F)=O(q^2/N)$
-- statement:
--   For every $n$ with $N\ge3$ and every $q$,
--   $$\mathrm{Adv}^{\mathrm{dist}}_q(D_{3PC},D_F)=O\Big(\frac{q^2}{N}\Big),$$
--   with an absolute constant.
--
--   It controls the degree-3 component of $\mu_{XoP[r]}$ (Lemma 6.9).
--
--   Differences from the source:
--   - encoding: no condition on n is printed → 2^n ≥ 3; reason: D_3PC samples 3 distinct inputs and is undefined for smaller N; the hypothesis only excludes undefined cases
--   - reading: O(·) in a statement that involves no fixed parameter → ∃ C > 0, quantified before every parameter (an absolute constant); reason: the statement has no parameter the constant could depend on
--   - encoding: a quantum oracle algorithm ends with a binary measurement (Π₀, Π₁ = I − Π₀) of its final state → the published QueryAlg is measured in the computational basis and an arbitrary output map out : (query register × workspace) → Bool gives the output bit; the workspace W and the final unitary U_q are arbitrary; reason: same class of algorithms: every binary projective measurement is a unitary followed by a computational-basis measurement
-- source:
--   Wonseok Choi, Minki Hhan, Junyoung Jang, Quantum Security of XOR of Permutations via Fourier Analysis, STOC 2027 submission #815 (October 2026), p. 28 (PDF p. 30), Lemma 6.8 (proof App. B.2, p. 44)

import Mathlib
import Definitions.Def_QuantumXoP_Security_Advantage
import Definitions.Def_QuantumXoP_Security_Planted

namespace QuantumXoP.Security

open QAlgorithms
open scoped ComplexConjugate

/-- Lemma 6.8 (p. 28): `Adv_q^dist(D_3PC, D_F) = O(q²/N)`, with an absolute constant. -/
theorem lemma_6_8 :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (hN : 3 ≤ 2 ^ n) (q : ℕ),
      AdvAtMost (Qubits n) (Qubits n) q (pc3Law n hN) (uniformF n)
        (C * (q : ℝ) ^ 2 / bigN n) := by sorry

end QuantumXoP.Security
