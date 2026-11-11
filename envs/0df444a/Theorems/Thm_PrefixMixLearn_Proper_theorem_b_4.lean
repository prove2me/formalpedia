-- Prove2me | Theorems.Thm_PrefixMixLearn_Proper_theorem_b_4
-- name    : PrefixMixLearn.Proper.theorem_b_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:46:28.201875+00:00
-- url     : https://prove2.me/theorems/bf21e27b-024d-45b3-bad5-c0a390730883
-- title:
--   Theorem B.4 — fresh factor-one selection from a finite list: exact call count m(1+Tn_f), Nm density evaluations
-- statement:
--   Let $T\ge1$, rational $0<\rho\le1$, $0<\delta<1$, and let $M_1,\dots,M_N$ ($N\ge1$) be laws on $\{0,1\}^T$ with rational densities, available to the selector only through exact density evaluations $x\mapsto M_i(x)$; let $n_f,B_f$ be from (B.2) and $B_s$, $m$ from (B.5). There is one fair-coin program with prefix-conditional access to the target $P$ which, given $(T,\rho,\delta,N)$, for every law $P$:
--   - makes exactly $m(1+Tn_f)$ target calls and exactly $Nm$ candidate-density evaluations on every run, and uses no candidate samples;
--   - returns on every run an index of the list (a list entry $\hat M$);
--   - has log-cost (bit time, calls, symbols, coins, output) at most $(T+N+m+n_f+B_f+B_s+\text{density bit length}+\text{input length}+2)^c$ for one fixed $c$;
--   - satisfies
--   $$\Pr\big[d_{TV}(P,\hat M)\le\min_i d_{TV}(P,M_i)+\rho\big]\ge1-\delta.$$
--   Moreover the target-call count is $O(T^5\rho^{-6}\log(2T/\rho)\log(2N/\delta))$. The theorem is the final selection step of the learner: it loses only an additive $\rho$, not a constant factor.
--
--   Differences from the source:
--   - reading: condition on any completed generation history H_gen determining the list → the list is an explicit input and the statement holds for every list; reason: conditionally on H_gen the list is fixed and the selector's randomness is fresh; quantifying over every list is that conditioning
--   - generalization: a nonempty list M_1, …, M_N of proper laws (laws in M_{2,α,T}) with exactly computable rational densities → any N ≥ 1 and any laws Ms : Fin N → Cube T → ℚ (rational-valued, IsLaw), not required to be α-balanced or two-product mixtures; reason: the selector and its guarantee never use balance or the mixture form, only exact rational densities; every list of proper laws with rational densities (in particular the carried dyadic mixtures) is such a list, so the statement specializes to the source
--   - reading: exactly computable rational densities; if candidate densities are computable in polynomial bit time with polynomial encoding length, all remaining resources are polynomial in these budgets and input lengths → the program reaches the candidates only through exact density evaluations: query 1 :: i :: x of `selectorOracle P Ms` returns M_{i+1}(x) as [numerator, denominator]; log-cost ≤ (T + N + m + n_f + B_f + B_s + densBits Ms + encLen input + 2)^c on every run, one c for all inputs, with densBits the largest bit length of a density value; reason: an evaluation is charged the length of its result, so the polynomial-time premise is exactly what turns this bound into the source's polynomial bound; one universal polynomial in the budgets, the density encoding length and the input length; log-cost bounds bit time, written and returned symbols, coins and output length
--   - encoding: the exact target-call count is m(1 + Tn_f), and there are Nm candidate-density evaluations → on every halted run, exactly m(1 + T n_f) queries of the form 0 :: h (target calls) and exactly N·m queries of the form 1 :: … (density evaluations); reason: target calls and density evaluations are the two query kinds of `selectorOracle`
--   - encoding: returns a list entry M̂ → outputs [i] with i < N, M̂ = M_{i+1}; the event compares tv P M̂ with every entry; reason: the index determines the entry; ≤ every entry + ρ is ≤ the minimum + ρ
--   - encoding: O(T⁵ρ⁻⁶ log(2T/ρ) log(2N/δ)) → ∃ C, ∀ T ≥ 1, ρ, δ, N ≥ 1: m(1 + T n_f) ≤ C T⁵ ρ⁻⁶ log(2T/ρ) log(2N/δ); reason: the O-constant is absolute
--   - encoding: "a prefix-conditional algorithm" (no machine is named; costs include bit operations, query writing, response processing, random bits, output length, input reading; learner randomness is fair bits) → a program of the fair-coin log-cost RAM `Machine` (instructions charged by bit lengths; `coin` draws one fair bit; `query` sends a 0/1 prefix to `condOracle P` and is charged for every cell read and written; `halt` for every output cell); a run's law is over the coins and the oracle replies; reason: the paper's model made explicit; one log-cost bound bounds every listed resource (calls, written and returned symbols, coins, bit time, output length)
--   - encoding: COND_P accepts prefixes with 0 ≤ |h| < T (Definition 2.1) → `selectorOracle P Ms` answers 0 :: h through `condOracle P`: a 0/1 list h with |h| < T and positive mass gets a fresh suffix with law P_h; every other target query gets the empty reply; reason: the paper never issues such queries; the empty reply carries no information about P; at zero-mass prefixes this is the source's "oracle required only at positive-mass prefixes"
-- source:
--   Saravanan, Proper Agnostic Learning of Two Balanced Product Distributions from Prefix-Conditional Samples, STOC 2027 submission (manuscript sha256 9c359910…), p. 20–21 (PDF 22–23), Theorem B.4, (B.4)–(B.6)

import Mathlib
import Definitions.Def_PrefixMixLearn_Proper_Laws
import Definitions.Def_PrefixMixLearn_Proper_Machine
import Definitions.Def_PrefixMixLearn_Proper_Budgets

namespace PrefixMixLearn.Proper

/-- Theorem B.4 (fresh factor-one selection): one fair-coin program which, given `T`, `ρ`, `δ`, `N`,
prefix-conditional access to `P` (queries `0 :: h`) and exact rational density evaluations of a
nonempty list of laws `M_1, …, M_N` (queries `1 :: i :: x`), makes exactly `m(1 + T n_f)` target
calls and exactly `N m` candidate-density evaluations on every run, always returns an index of the
list, has log-cost polynomial in its budgets, the density bit length and its input length, and with
probability at least `1 − δ` returns an entry within `ρ` of the best entry in total variation; and
the target-call count is `O(T⁵ ρ⁻⁶ log(2T/ρ) log(2N/δ))`. -/
theorem theorem_b_4 :
    (∃ (prog : Program) (c : ℕ),
      ∀ (T : ℕ), 1 ≤ T → ∀ (ρ δ : ℚ), 0 < ρ → ρ ≤ 1 → 0 < δ → δ < 1 →
      ∀ (N : ℕ), 1 ≤ N → ∀ (Ms : Fin N → Cube T → ℚ), (∀ i, IsLaw fun x => (Ms i x : ℝ)) →
      ∀ (P : Cube T → ℝ), IsLaw P →
        HaltsWithin prog (selectorOracle P Ms) (selectorInput T ρ δ N)
          (((T + N + selM ρ δ N + selNf T ρ + selBf T ρ + selBs ρ + densBits Ms +
            encLen (selectorInput T ρ δ N) + 2 : ℕ) : ℝ) ^ c) ∧
        QueryCountWhere prog (selectorOracle P Ms) (selectorInput T ρ δ N)
          (fun q => q.head? = some 0) (selM ρ δ N * (1 + T * selNf T ρ)) ∧
        QueryCountWhere prog (selectorOracle P Ms) (selectorInput T ρ δ N)
          (fun q => q.head? = some 1) (N * selM ρ δ N) ∧
        OutputsSatisfy prog (selectorOracle P Ms) (selectorInput T ρ δ N)
          (fun o => ∃ i : ℕ, i < N ∧ o = [i]) ∧
        1 - (δ : ℝ) ≤ outProb prog (selectorOracle P Ms) (selectorInput T ρ δ N)
          (fun o => ∃ i : Fin N, o = [i.val] ∧
            ∀ j : Fin N, tv P (fun x => (Ms i x : ℝ)) ≤ tv P (fun x => (Ms j x : ℝ)) + ρ)) ∧
    (∃ C : ℝ, ∀ (T : ℕ), 1 ≤ T → ∀ (ρ δ : ℚ), 0 < ρ → ρ ≤ 1 → 0 < δ → δ < 1 →
      ∀ (N : ℕ), 1 ≤ N →
        ((selM ρ δ N * (1 + T * selNf T ρ) : ℕ) : ℝ) ≤
          C * (T : ℝ) ^ 5 * (ρ : ℝ) ^ (-6 : ℤ) * Real.log (2 * T / ρ) *
            Real.log (2 * N / δ)) := by sorry

end PrefixMixLearn.Proper
