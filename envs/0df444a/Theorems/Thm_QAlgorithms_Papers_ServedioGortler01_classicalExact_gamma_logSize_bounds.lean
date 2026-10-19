-- Prove2me | Theorems.Thm_QAlgorithms_Papers_ServedioGortler01_classicalExact_gamma_logSize_bounds
-- name    : QAlgorithms.Papers.ServedioGortler01.classicalExact_gamma_logSize_bounds
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:05:18.219119+00:00
-- url     : https://prove2.me/theorems/67de8110-6680-451c-aba8-fe4b3bcd0604
-- title:
--   Classical membership-query complexity of exact learning: bounds via γ̂ and log|C|
-- statement:
--   Let $C$ be a class of concepts $c:\{0,1\}^n\to\{0,1\}$. Write $T(C)$ for the classical sample complexity of exact learning $C$ from membership queries: the least $T$ such that some randomized algorithm (a probability distribution over adaptive query trees) asking at most $T$ membership queries $x\mapsto c(x)$ outputs the target $c$ with probability at least $2/3$, for every $c\in C$. For $C'\subseteq C$, $a\in\{0,1\}^n$ and $b\in\{0,1\}$ let $\gamma^{C'}_{\langle a,b\rangle}=|\{c\in C':c(a)=b\}|/|C'|$, and for $|C|\ge2$ put
--
--   $$
--   \hat\gamma^{C}=\min_{C'\subseteq C,\ |C'|\ge2}\ \max_{a\in\{0,1\}^n}\ \min_{b\in\{0,1\}}\gamma^{C'}_{\langle a,b\rangle}.
--   $$
--
--   There are absolute constants $K_1,K_2,K_3>0$, independent of $n$ and $C$, such that for every $n$ and every class $C$:
--
--   1. (Lemma 4) if $|C|\ge2$, then $T(C)\ge K_1/\hat\gamma^{C}$;
--   2. (Lemma 8) $T(C)\ge K_2\log_2|C|$;
--   3. (Lemma 11) if $|C|\ge2$, then $T(C)\le K_3\log_2|C|/\hat\gamma^{C}$.
--
--   That is, $T(C)=\Omega(1/\hat\gamma^C)$, $T(C)=\Omega(\log|C|)$ and $T(C)=O(\log|C|/\hat\gamma^C)$. These are the classical bounds that, combined with their quantum analogues, show that quantum and classical exact learning from membership queries are polynomially equivalent in query complexity.
--
--   **Formalization Note** $\hat\gamma^C$ is the frozen `gammaParam`, which is only meaningful for $|C|\ge2$; that hypothesis is explicit. In (2) the cases $|C|\le1$ are harmless since $\log 0=\log 1=0$ in Lean. The query bound is required on every input string rather than only on targets in $C$; the resulting complexities coincide.
-- source:
--   Quantum versus Classical Learnability (Servedio, Gortler), arXiv:quant-ph/0007036v1, Lemmas 4, 8, 11, PDF p. 6. https://arxiv.org/abs/quant-ph/0007036v1 . PDF SHA-256: a8c814c9ef94c99ab58d4eeb5d4e98cec6f2cc24c6535e81e6ee3722ae1fdea3.

import Definitions.Def_QAlgorithms_Defs_LearningSeparation
set_option autoImplicit false

namespace QAlgorithms.Papers.ServedioGortler01

open QAlgorithms.Learning

/-- SG, Lemmas 4, 8 and 11 (pp.6, 8, 9; proofs in Appendix A, p.14). §3.2 writes `C` for a single
class `C_n` of concepts over `{0,1}^n` (p.4), so the constants are absolute: each is chosen before
`n` and `C`.

Let `T(C)` be the classical sample complexity of exact learning `C` from membership queries
(`classicalExactComplexity C`: the least `T` such that some randomized algorithm, i.e. a
probability distribution over adaptive query trees, making at most `T` queries outputs the target
`c` with probability `≥ 2/3` for every `c ∈ C`), and let `γ̂^C` be the parameter of p.6
(`gammaParam C`), defined for `|C| ≥ 2`.
1. (Lemma 4) `T(C) = Ω(1/γ̂^C)`: `T(C) ≥ K / γ̂^C` whenever `|C| ≥ 2`.
2. (Lemma 8) `T(C) = Ω(log |C|)`: `T(C) ≥ K log₂ |C|`.
3. (Lemma 11) `T(C) = O(log |C| / γ̂^C)`: `T(C) ≤ K log₂ |C| / γ̂^C` whenever `|C| ≥ 2`.

The hypothesis `|C| ≥ 2` is where `γ̂^C` is defined (otherwise `gammaParam` is the junk value `0`).
In (2) no size hypothesis is needed: `log₂ 0 = log₂ 1 = 0` in Lean. `classicalExactComplexity`
bounds the number of queries on every input string, the source only on targets `c ∈ C`; the two
complexities coincide (prune each tree at depth `T`). The output is the hypothesis function itself,
which is the source's "representation of a circuit `h` with `h ≡ c`" up to an encoding. -/
theorem classicalExact_gamma_logSize_bounds :
    (∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ) (C : Finset (Qubits n → Bool)), 2 ≤ C.card →
        K / gammaParam C ≤ (classicalExactComplexity C : ℝ)) ∧
    (∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ) (C : Finset (Qubits n → Bool)),
        K * Real.logb 2 (C.card : ℝ) ≤ (classicalExactComplexity C : ℝ)) ∧
    (∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ) (C : Finset (Qubits n → Bool)), 2 ≤ C.card →
        (classicalExactComplexity C : ℝ) ≤ K * Real.logb 2 (C.card : ℝ) / gammaParam C) := by
  sorry



end QAlgorithms.Papers.ServedioGortler01
