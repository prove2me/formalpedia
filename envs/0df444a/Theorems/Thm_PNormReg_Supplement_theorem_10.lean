-- Prove2me | Theorems.Thm_PNormReg_Supplement_theorem_10
-- name    : PNormReg.Supplement.theorem_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T17:57:39.003217+00:00
-- url     : https://prove2.me/theorems/2e41ffda-f12f-46e5-8193-175eb4b13000
-- title:
--   Theorem 10, p.35 — stochastic mirror descent for $\ell_2$-$\ell_q$ games: expected duality gap $\le\epsilon$ (43) in time $O(\mathrm{nnz}(M)+(n+d)\Lambda^2/((q-1)\epsilon^2))$ (44)
-- statement:
--   Let $M\in\mathbb R^{n\times d}$, $c\in\mathbb R^n$, $q\in(1,2]$, $p=q/(q-1)$, $\epsilon\in(0,1)$, and let $\Lambda$ satisfy (41): $\Lambda\ge\max\{1,\|M\|_{p,2}+\|c\|_p\}$. For the game $h(x,y)=y^\top Mx-c^\top y$ of (40), there is an algorithm returning $(\bar x,\bar y)\in B^d_2\times B^n_q$ with
--
--   $$\mathbb E\Big[\max_{y\in B^n_q}h(\bar x,y)-\min_{x\in B^d_2}h(x,\bar y)\Big]\le\epsilon\tag{43}$$
--
--   in time
--
--   $$O\Big(\mathrm{nnz}(M)+\frac{(n+d)\Lambda^2}{(q-1)\epsilon^2}\Big).\tag{44}$$
--
--   Precisely: there are one program and a constant $C>0$ such that on every input as above (with $n+d\ge1$) and every coin sequence the program has halted after $C\big(\mathrm{nnz}(M)+(n+d)\Lambda^2/((q-1)\epsilon^2)\big)$ steps with output in $B^d_2\times B^n_q$, and the duality gap of the output is integrable over the coins with expectation at most $\epsilon$.
--
--   This is the matrix-game solver that the finite-$p$ case of Theorem 7 and the high-accuracy algorithms run on every improvement step.
--
--   **Formalization Note** The time clause concerns an implementation, so the statement asserts that some program on the base machine achieves (43) and (44) together; it need not sample exactly as Algorithm 6 (whose sampling probabilities are real numbers, which fair coins cannot produce exactly in bounded time). Inequality (43) for Algorithm 6 itself is the published base milestone `PNormReg.theorem_10_gap`. Input: sparse layout of $M$, then $c$, header $q,\epsilon,\Lambda$; output $\bar x$ in cells $-1-j$, $\bar y$ in cells $-1-d-i$.
--
--   Differences from the source:
--   - reading: Algorithm 6 returns (x̄, ȳ) … in time O(·) → one admissible program of PNormReg.Machine whose output satisfies (43) and whose every run halts within the bound (44); reason: a running time is a property of an implementation; exact sampling with real-valued probabilities (lines 9, 12) has no worst-case bound with fair coins; (43) for Algorithm 6 itself is the published PNormReg.theorem_10_gap
--   - reading: O(nnz(M) + (n + d)Λ²/((q − 1)ϵ²)) → one constant C, no log factor, no n^τ; halted after ⌊C·(…)⌋ steps on every coin tape; reason: plain O; halting by step N is the same as work ≤ N on this machine
--   - reading: §5 assumes "without loss" M_{i:} ≠ 0 or c_i ≠ 0 for each i (footnote 5: discard such coordinates, extend ȳ by zero, return (0, 0) if all are discarded) → no such hypothesis; reason: footnote 5 makes the result hold for every M and c, and the discarding fits in O(nnz(M))
--   - encoding: E[duality gap] ≤ ϵ → the gap of the output is integrable over the fair-coin tape and its integral is ≤ ϵ; reason: integrability is stated because a non-integrable function would integrate to 0
--   - encoding: input M, c, q, ϵ, Λ → sparse layout of M (nonzero entries with positions), then c; header q, ϵ, Λ; output x̄ in cells −1 − j, ȳ in cells −1 − d − i; reason: a dense M cannot be read in nnz(M) time; the paper names no format
--   - encoding: M ∈ ℝ^{n×d} → 0 < n + d; reason: excludes only n = d = 0, where the bound is 0 and no run can halt
-- source:
--   Adil, Bullins, O'Carroll, Sidford, Solving p-norm regression in matrix multiplication time, STOC 2027 submission (manuscript sha256 e335b2fa…), Theorem 10, p.35 (PDF p.36); (40)–(41), p.33; Algorithm 6, p.34; nnz, p.7

import Mathlib
import Definitions.Def_PNormReg_Supplement_Layouts

open Matrix

namespace PNormReg

namespace Supplement

/-- **Theorem 10** (stochastic mirror descent for `ℓ₂`-`ℓ_q` games), (43) and (44) together.

Adil, Bullins, O'Carroll, Sidford, *Solving p-norm regression in matrix multiplication time*, STOC 2027
submission (manuscript sha256 e335b2fa…), Theorem 10, p.35 (PDF p.36); game (40) and normalization (41), p.33;
Algorithm 6, p.34; `nnz`, p.7.

"Under (41), Algorithm 6 returns (x̄, ȳ) ∈ B^d_2 × B^n_q satisfying
E[ max_{y∈B^n_q} h(x̄, y) − min_{x∈B^d_2} h(x, ȳ) ] ≤ ϵ (43) in time O( nnz(M) + (n + d)Λ^2/((q − 1)ϵ^2) ). (44)"

There are one admissible program `P` and `C > 0` such that for all `n, d` (not both `0`), `M ∈ ℝ^{n×d}`,
`c ∈ ℝ^n`, `q ∈ (1, 2]`, `ϵ ∈ (0, 1)` and `Λ` under (41) (`Λ ≥ 1`, `Λ ≥ ∥M∥_{p,2} + ∥c∥_p`,
`p = q/(q−1)`), with
`N = ⌊C·(nnz(M) + (n + d)Λ²/((q − 1)ϵ²))⌋`:
1. on every coin tape the run has halted after `N` steps (so its work is at most
   `C·(nnz(M) + (n + d)Λ²/((q − 1)ϵ²))`) with output `(x̄, ȳ)` in `B^d_2 × B^n_q`;
2. the duality gap `max_{y∈B^n_q} h(x̄, y) − min_{x∈B^d_2} h(x, ȳ)` of the output, `h(x, y) = y⊤Mx − c⊤y`, is
   integrable over the coin tape and its expectation is at most `ϵ`.

**Formalization Note.**
* The time clause (44) is a statement about an implementation on a machine, so the item is read as: some
  program on the base machine `PNormReg.Machine` achieves both (43) and (44). It need not reproduce
  Algorithm 6's sampling law exactly (lines 9 and 12 sample with real-valued probabilities, which fair
  coins cannot do exactly within a worst-case bound). (43) for Algorithm 6 itself, over its own samples,
  is the published `PNormReg.theorem_10_gap`.
* `O(·)` is a plain constant `C`: no log factor and no `n^τ`. The time bound holds on every tape; the
  expectation is over the fair-coin tape `coinTape`, with integrability stated (a Bochner integral of
  a non-integrable function would be `0`).
* §5 assumes "without loss" that `M_{i:} ≠ 0` or `c_i ≠ 0` for each `i`; footnote 5 removes the
  assumption (discard such coordinates, extend `ȳ` by zero, return `(0, 0)` if all are discarded). So
  the statement has no such hypothesis: the program may do the discarding within `O(nnz(M))`.
* Input: `sparseInput [q, ϵ, Λ] M c` (the nonzero entries of `M`, then `c`): reading a dense `M` would
  exceed `nnz(M)`. Output: `x̄_j` in cell `−1 − j`, `ȳ_i` in cell `−1 − d − i` (`outputPair`).
* `0 < n + d`: at `n = d = 0` the bound is `0` and no run can halt.
* The duality gap is the base mission's `PNormReg.dualityGap` of the original `(M, c)`. -/
theorem theorem_10 :
    ∃ (P : Program) (_ : Admissible P) (C : ℝ), 0 < C ∧
      ∀ (n d : ℕ), 0 < n + d → ∀ (M : Matrix (Fin n) (Fin d) ℝ) (c : Fin n → ℝ) (q ε Λ : ℝ),
        1 < q → q ≤ 2 → 0 < ε → ε < 1 → 1 ≤ Λ →
        rowNormP2 (conjExp q) M + lpNorm (conjExp q) c ≤ Λ →
        (∀ ω : ℕ → Bool,
          (run P (sparseInput [q, ε, Λ] M c) ω
            ⌊C * ((nnz M : ℝ) + ((n : ℝ) + d) * Λ ^ 2 / ((q - 1) * ε ^ 2))⌋₊).halted = true ∧
          l2Norm (outputPair d n (run P (sparseInput [q, ε, Λ] M c) ω
            ⌊C * ((nnz M : ℝ) + ((n : ℝ) + d) * Λ ^ 2 / ((q - 1) * ε ^ 2))⌋₊)).1 ≤ 1 ∧
          lpNorm q (outputPair d n (run P (sparseInput [q, ε, Λ] M c) ω
            ⌊C * ((nnz M : ℝ) + ((n : ℝ) + d) * Λ ^ 2 / ((q - 1) * ε ^ 2))⌋₊)).2 ≤ 1) ∧
        MeasureTheory.Integrable
          (fun ω => dualityGap M c q (outputPair d n (run P (sparseInput [q, ε, Λ] M c) ω
            ⌊C * ((nnz M : ℝ) + ((n : ℝ) + d) * Λ ^ 2 / ((q - 1) * ε ^ 2))⌋₊))) coinTape ∧
        ∫ ω, dualityGap M c q (outputPair d n (run P (sparseInput [q, ε, Λ] M c) ω
            ⌊C * ((nnz M : ℝ) + ((n : ℝ) + d) * Λ ^ 2 / ((q - 1) * ε ^ 2))⌋₊)) ∂coinTape ≤ ε := by sorry

end Supplement

end PNormReg
