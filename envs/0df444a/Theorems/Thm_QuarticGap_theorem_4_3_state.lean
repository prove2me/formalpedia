-- Prove2me | Theorems.Thm_QuarticGap_theorem_4_3_state
-- name    : QuarticGap.theorem_4_3_state
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:46:31.970187+00:00
-- url     : https://prove2.me/theorems/9feed148-c73e-4c03-9901-241915b57881
-- title:
--   Proof of Theorem 4.3, quantum upper bound (pp.31–32) — one phase query prepares $x_W/L_n$ with squared norm at least $1/(16n)$
-- statement:
--   Let $\lambda \in (0,1]$, $\alpha \in (0,1/(1+8\lambda)]$ be rational, and $n = 4^\ell \ge 4$. There is a quantum circuit, fixed before $W$, with one controlled phase query to $f(a,b) = W_{ab}$, whose final state has, in the component where the flag and the second register are both zero,
--   $$
--   \frac{z_0+r_W}{L_n} = \frac{x_W}{L_n}, \qquad L_n = \|z_0\|+\sqrt{(\lambda^2+\lambda^4)n},
--   $$
--   where $z_0 = (u,u,u+\lambda e_0,\alpha u)$ and $r_W = (0,\lambda v,\lambda^2 y,0)$. The squared norm of this component satisfies $D_W/L_n^2 \ge 1/L_n^2 \ge 1/(16n)$, because $\|z_0\|^2 = 3+\alpha^2+\lambda^2+2\lambda/\sqrt n \le 6$ and $\lambda^2+\lambda^4 \le 2$, so that $L_n^2 \le (\sqrt6+\sqrt{2n})^2 \le 16n$.
--
--   With Lemma 2.8 for $p_0 = 1/(16n)$ this gives the $O(\sqrt n)$ queries of the quantum upper bound.
--
--   **Formalization Note** The wires are the coordinate of $x_W$ (two block wires and the first register), then the second register, then further wires, among them the flag, all read as zero. The statement holds for every $W$.
--
--   Differences from the source:
--   - encoding: n a power of four, indices {0,1}^k → n = 4^ℓ, k = 2ℓ, √n = 2^ℓ; reason: the same values of n
--   - reading: the state preparation described step by step in the proof → the existence of a circuit over all unitary gates with at most one phase query and the stated amplitudes; reason: the proof gives the gates; gate counts of this step are part of the goal, not of this milestone
-- source:
--   Chakrabarti, Herman, Kim, Ozgul, The Quartic Gap Between Quantum and Dequantized Algorithms for Linear Algebra Is Tight, arXiv:2610.42069 (file sha256 9f68aaf9…), proof of Theorem 4.3 (quantum upper bound), pp.31–32

import Mathlib
import Definitions.Def_QuarticGap_Ahat

open QAlgorithms

namespace QuarticGap

/-- State preparation in the proof of the quantum upper bound of Theorem 4.3 (arXiv:2610.42069
(file sha256 9f68aaf9…), pp.31–32). A circuit fixed before `W`, with one controlled phase query to
`f(a, b) = W_ab`, prepares a state whose component in which the flag and the second register are both
zero is `(z₀ + r_W)/L_n = x_W/L_n`, of squared norm `D_W/L_n² ≥ 1/L_n² ≥ 1/(16n)`, since
`∥z₀∥² = 3 + α² + λ² + 2λ/√n ≤ 6`, `λ² + λ⁴ ≤ 2`, and `L_n² ≤ (√6 + √(2n))² ≤ 16n` for `n ≥ 4`.

**Formalization Note** `n ≥ 4` is `1 ≤ ℓ`. Wires: the coordinate `i` of `x_W` (two block wires and the
source's first register), then the second register of `2ℓ` wires, then `t` further wires, among them the
flag, all read as zero. The statement holds for every `W`, not only `W ∈ G`. -/
theorem theorem_4_3_state {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (lam α : ℚ) (hlam : 0 < lam ∧ lam ≤ 1)
    (hα : 0 < α ∧ α ≤ 1 / (1 + 8 * lam)) :
    (∃ (t : ℕ) (V : OracleCircuit UnitaryGates (fun _ : Fin 1 => 2 * ℓ + 2 * ℓ + 1)
        (2 + 2 * ℓ + 2 * ℓ + t)),
      V.queryCount 0 ≤ 1 ∧
      ∀ (W : SignMat ℓ) (i : Idx ℓ),
        act (V.unitary fun _ => phaseOracle (flatSign W)) (zeroKet (2 + 2 * ℓ + 2 * ℓ + t))
            (Fin.append (Fin.append i (zeros (2 * ℓ))) (zeros t)) =
          ((xW lam α W i / Ln ℓ lam α : ℝ) : ℂ)) ∧
    (∀ (W : SignMat ℓ) (i : Idx ℓ), z0 lam α i + rW lam W i = xW lam α W i) ∧
    (∀ W : SignMat ℓ, 1 / Ln ℓ lam α ^ 2 ≤ DW lam α W / Ln ℓ lam α ^ 2) ∧
    1 / (16 * 4 ^ ℓ) ≤ 1 / Ln ℓ lam α ^ 2 ∧
    ∑ i : Idx ℓ, z0 lam α i ^ 2 = 3 + (α : ℝ) ^ 2 + (lam : ℝ) ^ 2 + 2 * lam / 2 ^ ℓ ∧
    ∑ i : Idx ℓ, z0 lam α i ^ 2 ≤ 6 ∧
    (lam : ℝ) ^ 2 + (lam : ℝ) ^ 4 ≤ 2 ∧
    Ln ℓ lam α ^ 2 ≤ (Real.sqrt 6 + Real.sqrt (2 * 4 ^ ℓ)) ^ 2 ∧
    (Real.sqrt 6 + Real.sqrt (2 * 4 ^ ℓ)) ^ 2 ≤ 16 * 4 ^ ℓ := by sorry

end QuarticGap
