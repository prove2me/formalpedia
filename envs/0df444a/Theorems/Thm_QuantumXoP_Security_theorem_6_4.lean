-- Prove2me | Theorems.Thm_QuantumXoP_Security_theorem_6_4
-- name    : QuantumXoP.Security.theorem_6_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:06:57.993432+00:00
-- url     : https://prove2.me/theorems/ffdd2c95-6646-4bf1-95b4-1ab1c95ec925
-- title:
--   Theorem 6.4 — small-range distributions are $27q^3/R$-indistinguishable from random [Zha21]
-- statement:
--   For every integer $R\ge1$ and every $q$,
--   $$\mathrm{Adv}^{\mathrm{dist}}_q(S_R,S_\infty)\le\frac{27q^3}{R},$$
--   where $S_\infty=D_F$ is the uniform distribution on $F_n$.
--
--   The paper cites this result from Zhandry [Zha21] without proof and uses it, via Lemma 6.5, to prove Lemma 6.6.
--
--   Differences from the source:
--   - encoding: S_R samples g uniformly on the image I of f (Definition 6.3) → g is sampled uniformly on all of [R] = Fin R; reason: the law of h = g ∘ f is the same, since only the values of g on I are used
--   - encoding: a quantum oracle algorithm ends with a binary measurement (Π₀, Π₁ = I − Π₀) of its final state → the published QueryAlg is measured in the computational basis and an arbitrary output map out : (query register × workspace) → Bool gives the output bit; the workspace W and the final unitary U_q are arbitrary; reason: same class of algorithms: every binary projective measurement is a unitary followed by a computational-basis measurement
--   - generalization: n is a fixed positive integer (§2, p. 8) → every n : ℕ, including n = 0; reason: the case n = 0 is one extra instance; the statement specializes to every n ≥ 1
-- source:
--   Wonseok Choi, Minki Hhan, Junyoung Jang, Quantum Security of XOR of Permutations via Fourier Analysis, STOC 2027 submission #815 (October 2026), p. 26 (PDF p. 28), Theorem 6.4 (cited from [Zha21]); Definition 6.3

import Mathlib
import Definitions.Def_QuantumXoP_Security_Advantage
import Definitions.Def_QuantumXoP_Security_Planted

namespace QuantumXoP.Security

open QAlgorithms
open scoped ComplexConjugate

/-- Theorem 6.4 (p. 26, proven in [Zha21]): `Adv_q^dist(S_R, S_∞) ≤ 27q³/R` for every integer
`R ≥ 1`, where `S_∞ = D_F`. -/
theorem theorem_6_4 (n R : ℕ) [NeZero R] (q : ℕ) :
    AdvAtMost (Qubits n) (Qubits n) q (smallRange n R) (uniformF n)
      (27 * (q : ℝ) ^ 3 / R) := by sorry

end QuantumXoP.Security
