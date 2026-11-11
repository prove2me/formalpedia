-- Prove2me | Theorems.Thm_QuantumXoP_Security_lemma_6_2
-- name    : QuantumXoP.Security.lemma_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:06:46.178013+00:00
-- url     : https://prove2.me/theorems/d7a2acb4-b46a-4970-86fb-21cfb75a7550
-- title:
--   Lemma 6.2 — query-dependent bounds for the components of degree 2, 3, 4, 6
-- statement:
--   Let $n\ge5$, $2\le r\le N/16$, $q\le N/57774$, and let $P_A$ be the representing polynomial of a $q$-query algorithm $A$. Then for $d=2,3,4,6$,
--   $$\big|\langle\mu^{=d}_{XoP[r]},P_A\rangle\big|=O\Big(\frac{q^3}{N^r}\Big),$$
--   with a constant depending only on $r$.
--
--   Together with Lemma 5.2 for the other degrees it gives Lemma 6.1.
--
--   Differences from the source:
--   - reading: O(·), the hidden factor depending only on r (abstract; p. 14; p. 34) → ∃ C > 0, quantified after r and before n, q, the workspace, the algorithm and the output map; reason: the paper fixes what the hidden constant may depend on
--   - encoding: a quantum oracle algorithm ends with a binary measurement (Π₀, Π₁ = I − Π₀) of its final state → the published QueryAlg is measured in the computational basis and an arbitrary output map out : (query register × workspace) → Bool gives the output bit; the workspace W and the final unitary U_q are arbitrary; reason: same class of algorithms: every binary projective measurement is a unitary followed by a computational-basis measurement
-- source:
--   Wonseok Choi, Minki Hhan, Junyoung Jang, Quantum Security of XOR of Permutations via Fourier Analysis, STOC 2027 submission #815 (October 2026), p. 26 (PDF p. 28), Lemma 6.2

import Mathlib
import Definitions.Def_QuantumXoP_Security_Advantage

namespace QuantumXoP.Security

open QAlgorithms
open scoped ComplexConjugate

/-- Lemma 6.2 (p. 26): if `n ≥ 5`, `2 ≤ r ≤ N/16` and `q ≤ N/57774`, then
`|⟨μ^{=d}_{XoP[r]}, P_A⟩| = O(q³/N^r)` for `d = 2, 3, 4, 6` and every `q`-query algorithm `A`, the
constant depending only on `r`. -/
theorem lemma_6_2 (r : ℕ) (hr : 2 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 5 ≤ n → 16 * r ≤ 2 ^ n → ∀ q : ℕ, 57774 * q ≤ 2 ^ n →
      ∀ (W : Type) [Fintype W] [DecidableEq W] (A : QueryAlg (Qubits n) (Qubits n) W q)
        (out : (Qubits n × Qubits n) × W → Bool), ∀ d ∈ ({2, 3, 4, 6} : Finset ℕ),
        ‖innerF (degComp (density (xopLaw n r)) d) (repPoly A out)‖ ≤
          C * (q : ℝ) ^ 3 / bigN n ^ r := by sorry

end QuantumXoP.Security
