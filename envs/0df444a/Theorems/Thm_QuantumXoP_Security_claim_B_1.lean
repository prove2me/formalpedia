-- Prove2me | Theorems.Thm_QuantumXoP_Security_claim_B_1
-- name    : QuantumXoP.Security.claim_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:06:35.578875+00:00
-- url     : https://prove2.me/theorems/13d7567d-cbae-48c3-8003-1c189a5792c7
-- title:
--   Claim B.1 — decisional search: $\mathrm{Adv}_q^{\mathrm{dist}}(S_M,Z_M)\le16q^2/M$
-- statement:
--   Let $M\ge1$. Let $Z_M$ always output the zero function $b_\emptyset:[M]\to\{0,1\}$, and let $S_M$ sample $z\leftarrow[M]$ uniformly and output the indicator $b_z(j)=[\![j=z]\!]$. For every $q$, algorithms with the standard oracle $|j,b\rangle\mapsto|j,b\oplus x_j\rangle$ satisfy
--   $$\mathrm{Adv}^{\mathrm{dist}}_q(S_M,Z_M)\le\frac{16q^2}{M}.$$
--
--   It is the search lower bound behind the planted 3-collision bound, Lemma 6.8.
--
--   Differences from the source:
--   - encoding: no condition on M is printed → M ≥ 1 ([NeZero M]); reason: S_M samples z ← [M], undefined for M = 0
--   - encoding: a quantum oracle algorithm ends with a binary measurement (Π₀, Π₁ = I − Π₀) of its final state → the published QueryAlg is measured in the computational basis and an arbitrary output map out : (query register × workspace) → Bool gives the output bit; the workspace W and the final unitary U_q are arbitrary; reason: same class of algorithms: every binary projective measurement is a unitary followed by a computational-basis measurement
-- source:
--   Wonseok Choi, Minki Hhan, Junyoung Jang, Quantum Security of XOR of Permutations via Fourier Analysis, STOC 2027 submission #815 (October 2026), p. 43 (PDF p. 45), Claim B.1

import Mathlib
import Definitions.Def_QuantumXoP_Security_Advantage
import Definitions.Def_QuantumXoP_Security_Planted

namespace QuantumXoP.Security

open QAlgorithms
open scoped ComplexConjugate

/-- Claim B.1 (p. 43): with Boolean oracles on `[M]`, `Adv_q^dist(S_M, Z_M) ≤ 16q²/M` for every
`q`, where `Z_M` is the all-zero function and `S_M` the indicator of a uniform `z ← [M]`. -/
theorem claim_B_1 (M : ℕ) [NeZero M] (q : ℕ) :
    AdvAtMost (Fin M) Bool q (indicatorLaw M) (zeroLaw M) (16 * (q : ℝ) ^ 2 / M) := by sorry

end QuantumXoP.Security
