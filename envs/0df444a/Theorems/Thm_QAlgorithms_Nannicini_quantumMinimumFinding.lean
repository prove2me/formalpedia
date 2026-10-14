-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_quantumMinimumFinding
-- name    : QAlgorithms.Nannicini.quantumMinimumFinding
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:46:01.329754+00:00
-- url     : https://prove2.me/theorems/dd67bf1e-9170-4f8d-999b-25d7a8113079
-- title:
--   Quantum minimum finding (Dürr–Høyer), with explicit bit width, interruption and gate model
-- statement:
--   Let $f : \{0,1\}^n \to \mathbb{Z}$ take values of bit width $b$, i.e. $|f(j)| < 2^b$ for all $j$, and let $U_f : |j\rangle|k\rangle \mapsto |j\rangle|k \oplus f(j)\rangle$ evaluate $f$ in binary. Algorithm 2 with budget $T$ starts from a uniformly random incumbent $\ell$ and repeatedly runs Algorithm 1 (search with an unknown number of marked items) with the marking unitary $U_m : |j\rangle|y\rangle \mapsto |j\rangle|y \oplus \mathbb{I}(f(j) < f(\ell))\rangle$, replacing $\ell$ by the returned index $k$ whenever $f(k) < f(\ell)$; a call of Algorithm 1 that would exceed the budget is interrupted at the $T$-th application of $U_f$, and the algorithm then returns $\ell$. Each application of $U_m$ counts as one application of $U_f$ and is charged $3n + 2b + 1$ additional gates; each round of Algorithm 1 with $m$ qubits of precision is charged $m + m(m+1)/2$ further gates (Hadamards and the inverse QFT).
--
--   There are absolute constants $c, C > 0$ such that for every $n$, $b$, every such $f$ and every $\delta \in (0,1)$ the following holds. Run Algorithm 2 independently $k = \lceil \log_3(1/\delta) \rceil$ times with budget $T = \lceil c\sqrt{2^n} \rceil$ and output an $f$-minimal one of the $k$ returned indices. Then:
--
--   1. with probability at least $1 - \delta$ the output is a global minimizer of $f$;
--   2. on every outcome, the total number of applications of $U_f$ (including the $k$ evaluations used to select the output) is at most
--   $$
--   C\sqrt{2^n}\,\bigl(1 + \log(1/\delta)\bigr),
--   $$
--   and the number of additional gates is at most $C\sqrt{2^n}\,(n + b + 1)\,(1 + \log(1/\delta))$.
--
--   This is the quadratic quantum speedup for unstructured minimization, the basis of the optimization applications of Grover search.
--
--   **Formalization Note** The source's $\tilde O(\sqrt{2^n})$ gate bound is stated with the suppressed polylogarithmic factors $n + b + 1$ and $1 + \log(1/\delta)$ explicit, the interruption rule for the budget is made explicit, and $T$, $k$ are the choices of the source's proof. Algorithm 1 is the shared formalization of the earlier corollary; the outcome law is a weight on (returned index, applications of $U_f$, gates).
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 96, Theorem 4.31. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_AmplitudeEstimation
import Definitions.Def_QAlgorithms_Nannicini_Ch04c_Model
set_option autoImplicit false

namespace QAlgorithms.Nannicini

open scoped ENNReal











/-- Corrected statement. Nannicini p.96, Theorem 4.31 (Quantum minimum finding; Dürr–Høyer).
Printed: for `f : {0,1}^n → ℤ` evaluated in binary by `U_f` and `δ > 0`, Alg. 2 determines the
global minimum of `f` with probability at least `1 − δ` using `O(√2^n log 1/δ)` applications of
`U_f` in total and `Õ(√2^n)` additional gates.

Changed: (1) the bit width `b` of the values of `f` (`|f(j)| < 2^b`) is a named parameter, the
constants are uniform in it, and the gate bound is `C √2^n (n + b + 1)(1 + log 1/δ)` in the cost
model of this section (`mfStepGates`, `mfRoundOverhead`): the factors `n + b + 1` and
`1 + log 1/δ` are the polylogarithmic factors that `Õ` suppresses (Def. 1.11), made explicit;
(2) a call of Alg. 1 that would exceed the budget `T` is interrupted at the `T`-th application of
`U_f` and Alg. 2 then returns its incumbent (`minFindLoop`); (3) the budget and the number of
repetitions are the proof's (p.97): `T = ⌈c √2^n⌉` for an absolute constant `c` (the proof's
`3t̄ = 9c'√2^n`, `c'` the constant of Cor. 4.30), and `k = ⌈log₃ 1/δ⌉` independent runs, the
answer being an `f`-minimal one of the `k` returned indices, which is a global minimizer iff
some returned index is (its selection costs `k` more evaluations, counted); (4) `δ < 1` and
`log 1/δ` read as `1 + log 1/δ`, since at least one evaluation is needed for every `δ < 1`.

Why: each application of `U_m` compares a `b`-bit value with `f(ℓ)` (`Θ(b)` gates) and the source
never fixes `b`, so `Õ(√2^n)` is false when `b` is not polylogarithmic in `2^n` unless `b` is
among the suppressed parameters; and without interruption a call of Alg. 1 with no marked item
(always the case once `ℓ` is the minimum) enumerates all `2^n` strings, so the printed loop
condition alone does not give the `O(√2^n log 1/δ)` total. -/
theorem quantumMinimumFinding :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (n b : ℕ) (f : Qubits n → ℤ), (∀ j, |f j| < 2 ^ b) →
      ∀ δ : ℝ, 0 < δ → δ < 1 →
        ENNReal.ofReal (1 - δ) ≤
            minFindRepeatProb f b ⌈c * Real.sqrt ((2 : ℝ) ^ n)⌉₊ ⌈Real.logb 3 (1 / δ)⌉₊
              (fun outs => ∃ i, ∀ j, f (outs i).1 ≤ f j) ∧
        ∀ outs : Fin ⌈Real.logb 3 (1 / δ)⌉₊ → Qubits n × ℕ × ℕ,
          (∏ i, minFindWeight f b ⌈c * Real.sqrt ((2 : ℝ) ^ n)⌉₊ (outs i)) ≠ 0 →
            (((∑ i, (outs i).2.1) + ⌈Real.logb 3 (1 / δ)⌉₊ : ℕ) : ℝ) ≤
                C * Real.sqrt ((2 : ℝ) ^ n) * (1 + Real.log (1 / δ)) ∧
            (((∑ i, (outs i).2.2) + ⌈Real.logb 3 (1 / δ)⌉₊ * mfStepGates n b : ℕ) : ℝ) ≤
                C * Real.sqrt ((2 : ℝ) ^ n) * ((n + b + 1 : ℕ) : ℝ) * (1 + Real.log (1 / δ)) := by
  sorry

end QAlgorithms.Nannicini
