-- Prove2me | Theorems.Thm_PackingLPAccel_theorem_1_1
-- name    : PackingLPAccel.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:43:32.511373+00:00
-- url     : https://prove2.me/theorems/d86f8ea0-422c-408a-8c02-f8c349992b07
-- title:
--   Theorem 1.1 — a deterministic width-independent $(1-\epsilon)$-approximation for packing LPs in $\tilde O(\epsilon^{-1})$ depth (corrected: nonempty columns, factor $1+\epsilon^{-1}$)
-- statement:
--   There is one program of the exact-arithmetic work-depth language, with no oracle and no randomness, such that the following holds for every $c$, with constants $C,K$ depending only on $c$. Let $A\in\mathbb R^{m\times n}_{\ge0}$, $n\ge1$, have no empty column, let $\epsilon>0$ with $\epsilon^{-1}\le(m+n)^c$, and let $A$ be given by any enumeration of its $N=\mathrm{nnz}(A)$ nonzero entries. Then the program halts with an output $\hat x$ satisfying
--
--   $$\hat x\ge0,\qquad A\hat x\le\mathbf 1,\qquad\langle\mathbf 1,\hat x\rangle\ge(1-\epsilon)\mathrm{OPT},$$
--
--   with depth at most $C(1+\epsilon^{-1})(\log_2(m+n)+1)^K$ and work at most $C\,\mathrm{nnz}(A)(1+\epsilon^{-1})(\log_2(m+n)+1)^K$.
--
--   No bound depends on the width or the size of the entries of $A$. This is the main result of the paper: an accelerated, deterministic, width-independent solver that is both nearly linear in time and polylogarithmic in depth at fixed accuracy.
--
--   Differences from the source:
--   - correction: A ∈ ℝ^{m×n}_{≥0} → every column of A has a nonzero entry; reason: A = 0 ∈ ℝ^{1×1} has OPT = +∞, and no x̂ satisfies ⟨1,x̂⟩ ≥ (1−ε)OPT for ε < 1; Definition 3.1 and p.10 already exclude empty columns
--   - correction: Õ(·ε⁻¹) for every ε > 0 → the factor 1 + ε⁻¹; reason: any run has depth at least 1 while Cε⁻¹polylog(m,n) < 1 for large ε at fixed m, n; for ε ≤ 1 the factor is at most 2ε⁻¹
--   - reading: "There is a … algorithm", PRAM, the list of p.8 → one program of the language Stmt/Eval (CREW, snapshot parFor, exclusive write), with no log, exp, floor or integer multiplication; reason: the paper names only PRAM and the p.8 list; the list is taken literally, as the non-weaker reading, although the paper's proof evaluates log (p.28)
--   - generalization: the input is A → every enumeration of the nonzero entries, in any order; reason: a fixed order is one such enumeration
--   - encoding: ε⁻¹ ≤ O(poly(m,n)) (footnote 2) → ε⁻¹ ≤ (m+n)^c for every c, with one program before c and C, K after; reason: m + n ≥ 2 absorbs the constant of O(poly)
--   - encoding: Õ(·), time, n unrestricted → C·(…)·lg(m+n)^K, work, 0 < n; reason: the meaning of Õ on p.1, of time on p.8, and n = 0 is the empty program
-- source:
--   Chen, Chen, Graur, Sidford, Accelerated Parallel Algorithms for Packing Linear Programming, STOC 2027 submission (manuscript sha256 1dac7711…), Theorem 1.1, p.2 (pdf 3); footnotes 2–4, p.1 (pdf 2); computational model, p.8 (pdf 9)

import Mathlib
import Definitions.Def_PackingLPAccel_PackingLP

namespace PackingLPAccel

/-- **Theorem 1.1** (Chen, Chen, Graur, Sidford, STOC 2027 submission, manuscript sha256 1dac7711…,
p.2): there is a deterministic algorithm that, given a nonnegative `A` and `ε > 0`, obtains a
`(1-ε)`-multiplicative approximation of the packing LP in `Õ(ε⁻¹)` depth and `Õ(nnz(A) ε⁻¹)` time.

**Formalization Note.** One program `P`, chosen before everything else. The footnote's
`ε⁻¹ ≤ O(poly(m, n))` is `ε⁻¹ ≤ (m+n)^c` for every `c`, and only `C`, `K` depend on `c`.
`Õ` is `C · (…) · (⌊log₂(m+n)⌋+1)^K`, with no width, entry size or `1 / min A` in the bound.
`noOracle`: the program has no oracle. Two corrections of the printed statement: every column is
nonempty (`A = 0` has `OPT = +∞`), and the factor is `1 + ε⁻¹` (a depth bound below `1` is impossible
for large `ε`). -/
theorem theorem_1_1 :
    ∃ P : Stmt, ∀ c : ℕ, ∃ C K : ℕ,
      ∀ (m n : ℕ) (_ : 0 < n) (A : Matrix (Fin m) (Fin n) ℝ) (_ : ∀ i j, 0 ≤ A i j)
        (_ : ∀ j, ∃ i, A i j ≠ 0) (ε : ℝ) (_ : 0 < ε) (_ : ε⁻¹ ≤ ((m + n : ℕ) : ℝ) ^ c)
        (N : ℕ) (e : Fin N → Fin m × Fin n) (_ : IsNonzeroEnum A e),
      ∃ (s' : State) (w d : ℕ), Eval noOracle P (goalInit A ε e) s' w d ∧
        Feasible A (goalOutput N s') ∧
        (1 - ε) * packingOpt A ≤ ∑ j, goalOutput (n := n) N s' j ∧
        (w : ℝ) ≤ C * N * (1 + ε⁻¹) * (lg (m + n) : ℝ) ^ K ∧
        (d : ℝ) ≤ C * (1 + ε⁻¹) * (lg (m + n) : ℝ) ^ K := by sorry

end PackingLPAccel
