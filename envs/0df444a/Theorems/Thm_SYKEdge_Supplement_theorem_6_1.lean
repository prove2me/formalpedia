-- Prove2me | Theorems.Thm_SYKEdge_Supplement_theorem_6_1
-- name    : SYKEdge.Supplement.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:24:26.395714+00:00
-- url     : https://prove2.me/theorems/01d78045-a9e3-48a3-9dab-ace36cca0733
-- title:
--   Theorem 6.1 — $\Omega(\sqrt n/k)\le\mathbb E\|H_{k-\mathrm{QSG}}\|_{op}\le O(\sqrt{n/k})$ for $k$-local quantum spin glasses
-- statement:
--   For integers $n\ge k\ge1$ let $H_{k-\mathrm{QSG}}=m^{-1/2}\sum_{P\in\mathcal P_{n,k}}g_PP$, $m=3^k\binom nk$, be the $k$-local quantum spin glass Hamiltonian on $n$ qubits, where $\mathcal P_{n,k}$ is the set of Pauli strings of weight exactly $k$ and $(g_P)$ are i.i.d. $N(0,1)$. There are absolute constants $c,C>0$ such that for all $n\ge k\ge1$ with $k\le\sqrt n/2$,
--   $$c\,\frac{\sqrt n}k\ \le\ \mathbb E_g\|H_{k-\mathrm{QSG}}\|_{op}\ \le\ C\sqrt{\frac nk}.$$
--
--   The upper bound improves the previous $O(\sqrt n)$ of [BCD24] by a factor $\sqrt k$; the conjectured truth is $\Theta(\sqrt n/k)$.
--
--   **Formalization Note** The lower bound is quoted from [BCD24] on p.5 and is not re-proved in the paper; it is part of the labelled theorem and is stated here.
--
--   Differences from the source:
--   - encoding: Ω(√n/k) and O(√(n/k)) → absolute constants c, C > 0 quantified before n and k; reason: the paper's constants are absolute (footnote 20, p.36)
--   - encoding: P_{n,k} ⊆ {Id, X, Y, Z}^{⊗n}, the 2^n × 2^n matrices of weight k → the published QPSpinProfile.PauliString n k (words Fin n → Fin 4 with exactly k non-identity letters) and their tensor-product matrices PauliString.mat on Qubits n; reason: word ↦ tensor product is a bijection onto P_{n,k}; m = 3^k (n choose k) is written as that number, equal to the cardinality
-- source:
--   Basu, Kothari, Midha, Sharp Bounds on Ground State Energy of the SYK Model, arXiv:2607.27185v2, Theorem 6.1, p.42 (PDF p.42); informal version Theorem 1.8 and definition of H_{k−QSG}, p.5

import Mathlib
import Definitions.Def_SYKEdge_Hamiltonian
import Definitions.Def_SYKEdge_MatrixNorms
import Definitions.Def_SYKEdge_Supplement_QSG

open Matrix MeasureTheory

namespace SYKEdge.Supplement

open SYKEdge QPSpinProfile

/-- **Theorem 6.1** (Improved Bounds for Spectral Norm of Quantum Spin Glasses), A. Basu,
P. K. Kothari, S. Midha, *Sharp Bounds on Ground State Energy of the SYK Model*,
arXiv:2607.27185v2, p.42 (PDF p.42); stated informally as Theorem 1.8, p.5.

For any `n ⩾ k ⩾ 1` with `k ⩽ √n/2`, `Ω(√n/k) ⩽ E_g ‖H_{k−QSG}‖_op ⩽ O(√(n/k))`.

**Formalization Note.**
* `Ω(·)` and `O(·)` are absolute constants `c, C > 0` chosen before `n` and `k`.
* `H_{k−QSG} = (3^k (n choose k))^{−1/2} Σ_{P ∈ 𝒫_{n,k}} g_P P` is `qsg n k g`, with `𝒫_{n,k}` the
  published `QPSpinProfile.PauliString n k` (weight exactly `k`); `E_g` is the integral against the
  i.i.d. `N(0,1)` law `stdGauss (PauliString n k)`; `‖·‖_op` is `SYKEdge.opNorm` on `(ℂ²)^{⊗n}`.
* Both bounds are part of the theorem (the lower bound is the one of [BCD24] quoted on p.5). -/
theorem theorem_6_1 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ n k : ℕ, 1 ≤ k → k ≤ n → (k : ℝ) ≤ Real.sqrt n / 2 →
        c * (Real.sqrt n / k) ≤ ∫ g, opNorm (qsg n k g) ∂stdGauss (PauliString n k) ∧
        ∫ g, opNorm (qsg n k g) ∂stdGauss (PauliString n k) ≤ C * Real.sqrt ((n : ℝ) / k) := by sorry

end SYKEdge.Supplement
