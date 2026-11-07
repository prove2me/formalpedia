-- Prove2me | Theorems.Thm_QCopyMono_lemma_7
-- name    : QCopyMono.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:45:46.963046+00:00
-- url     : https://prove2.me/theorems/9e3247ab-6878-4417-882e-a3a9bc73ac16
-- title:
--   Lemma 7 (Variance of the path estimator) — $\mathrm{Var}(\hat p_d)\le C_{\mathrm{est}}t_d/(m\sqrt n)$
-- statement:
--   There are absolute constants $n_0$ and $C_{\mathrm{est}}>0$ such that the following holds for every constant $0<c_0\le1$ defining $t_d=\max\{1,\lfloor c_0\varepsilon\sqrt n\,d^{-5/8}\rfloor\}$. Let $n\ge n_0$, $n^{-1/2}\le\varepsilon\le1/2$ and $d\in\mathcal D_n$, and let the estimator
--   $$
--   \hat p_d=\tfrac12\overline U_d-\tfrac14\overline V_d
--   $$
--   of eq. (20) use $m\ge1$ independent outcomes of each observable. Whenever $I[f]\le2\sqrt n$,
--   $$
--   \mathrm{Var}(\hat p_d)\le C_{\mathrm{est}}\,\frac{t_d}{m\sqrt n}.
--   $$
--   Together with Lemma 6 this gives the copy count $O(n/\varepsilon^3)$ of the path tester.
--
--   Differences from the source:
--   - generalization: t_d as in Lemma 6 (the c_0 of Lemma 6) → t_d built from every c_0 ∈ (0, 1], with C_est and n_0 independent of c_0; reason: Lemma 6 provides c_0 ≤ 1, so its t_d is an instance; the proof uses only t_d ≤ max{1, ε√n}
--   - reading: "Let n ≥ n_0 … There is a constant C_est > 0" → C_est and n_0 chosen before c_0, n, ε, d, m, f, with n_0 this lemma's own; reason: C_est is used as an absolute constant in m_d (p.10), and the proof increases the absolute n_0 if necessary (p.40)
--   - encoding: Var(p̂_d) over the 2m independent measurement outcomes → ProbabilityTheory.variance of p̂_d under the product of m copies of the Q_d outcome law and m copies of the H_d ⊗ Z outcome law; reason: same random variable; the law is a finitely supported probability measure
--   - encoding: d ∈ D_n = {1, 2, 4, …, 2^{⌊log_2 n⌋}} → d = 2^j with 2^j ≤ n; reason: the same set
-- source:
--   Naik, Quantum Copy Complexity of Testing Monotonicity and Other Properties, STOC 2027 submission (manuscript sha256 10fb417512cedc538a3dc512c3cd893806335ae8e073ebaf1deeeab8e5dac528), Lemma 7, p.15, eq. (21) (proof in Appendix A.2, pp.39–42)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QCopyMono_Influence
import Definitions.Def_QCopyMono_PathExperiment
import Definitions.Def_QCopyMono_ObsLaw

namespace QCopyMono

open QAlgorithms

/-- Naik, *Quantum Copy Complexity of Testing Monotonicity and Other Properties*, STOC 2027
submission (manuscript sha256 10fb4175…dac528), Lemma 7 (Variance of the path estimator), p.15
(proof in Appendix A.2, pp.39–42): for `n ≥ n₀`, `n^{−1/2} ≤ ε ≤ 1/2`, `d ∈ Dₙ` with `t_d` as in
Lemma 6, and the estimator (20) using `m ≥ 1` independent outcomes of each observable, there is
a constant `C_est > 0` such that `I[f] ≤ 2√n` implies `Var(p̂_d) ≤ C_est t_d/(m√n)` (eq. (21)).

**Formalization Note.** `C_est` and `n₀` are absolute: they are chosen before `c₀`, `n`, `ε`,
`d`, `m`, `f`. The bound holds for `t_d` built from every constant `0 < c₀ ≤ 1`, which covers
the `c₀` of Lemma 6 (the proof uses only `t_d ≤ max{1, ε√n}`, and increases `n₀` if necessary).
`Var` is the variance of `p̂_d` under the actual joint law of the `2m` measurement outcomes
(`pathSampleLaw`), a finitely supported probability measure. `d = 2^j` with `2^j ≤ n`. -/
theorem lemma_7 :
    ∃ n₀ : ℕ, 0 < n₀ ∧ ∃ Cest : ℝ, 0 < Cest ∧ ∀ c₀ : ℝ, 0 < c₀ → c₀ ≤ 1 →
      ∀ n : ℕ, n₀ ≤ n → ∀ ε : ℝ, (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ ε → ε ≤ 1 / 2 →
        ∀ j : ℕ, 2 ^ j ≤ n → ∀ m : ℕ, 1 ≤ m → ∀ f : Qubits n → Bool,
          influence f ≤ 2 * Real.sqrt n →
            ProbabilityTheory.variance (pathEstimate m)
                (pathSampleLaw n ε (pathLen c₀ ε n ((2 : ℝ) ^ j)) m f) ≤
              Cest * (pathLen c₀ ε n ((2 : ℝ) ^ j) : ℝ) / (m * Real.sqrt n) := by sorry

end QCopyMono
