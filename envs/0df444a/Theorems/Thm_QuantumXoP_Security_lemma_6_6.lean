-- Prove2me | Theorems.Thm_QuantumXoP_Security_lemma_6_6
-- name    : QuantumXoP.Security.lemma_6_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:07:12.251963+00:00
-- url     : https://prove2.me/theorems/99aa2e50-089e-4a0c-a603-afad34290fc4
-- title:
--   Lemma 6.6 — $\mathrm{Adv}_q^{\mathrm{dist}}(D_{PC},D_F)=O(q^3/N^2)$
-- statement:
--   For every $n$ with $N\ge2$ and every $q$,
--   $$\mathrm{Adv}^{\mathrm{dist}}_q(D_{PC},D_F)=O\Big(\frac{q^3}{N^2}\Big),$$
--   with an absolute constant.
--
--   It controls the degree-2 component of $\mu_{XoP[r]}$ (Lemma 6.7) and, through Appendix B, the planted 3-collision, multi-collision and 4-XOR distributions.
--
--   Differences from the source:
--   - encoding: no condition on n is printed → 2^n ≥ 2; reason: D_PC samples 2 distinct inputs and is undefined for smaller N; the hypothesis only excludes undefined cases
--   - reading: O(·) in a statement that involves no fixed parameter → ∃ C > 0, quantified before every parameter (an absolute constant); reason: the statement has no parameter the constant could depend on
--   - encoding: a quantum oracle algorithm ends with a binary measurement (Π₀, Π₁ = I − Π₀) of its final state → the published QueryAlg is measured in the computational basis and an arbitrary output map out : (query register × workspace) → Bool gives the output bit; the workspace W and the final unitary U_q are arbitrary; reason: same class of algorithms: every binary projective measurement is a unitary followed by a computational-basis measurement
-- source:
--   Wonseok Choi, Minki Hhan, Junyoung Jang, Quantum Security of XOR of Permutations via Fourier Analysis, STOC 2027 submission #815 (October 2026), p. 27 (PDF p. 29), Lemma 6.6

import Mathlib
import Definitions.Def_QuantumXoP_Security_Advantage
import Definitions.Def_QuantumXoP_Security_Planted

namespace QuantumXoP.Security

open QAlgorithms
open scoped ComplexConjugate

/-- Lemma 6.6 (p. 27): `Adv_q^dist(D_PC, D_F) = O(q³/N²)`, with an absolute constant. -/
theorem lemma_6_6 :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (hN : 2 ≤ 2 ^ n) (q : ℕ),
      AdvAtMost (Qubits n) (Qubits n) q (pcLaw n hN) (uniformF n)
        (C * (q : ℝ) ^ 3 / bigN n ^ 2) := by sorry

end QuantumXoP.Security
