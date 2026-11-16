-- Prove2me | Theorems.Thm_QuantumStateIdentity321_Schur_Supplement_theorem_5_6
-- name    : QuantumStateIdentity321.Schur.Supplement.theorem_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:03:10.025203+00:00
-- url     : https://prove2.me/theorems/a94bfd4b-346c-4095-83d9-8abde3876da5
-- title:
--   Theorem 5.6 — lower bound $\Omega(\log(n/\delta)/\log(1/\varepsilon))$ copies for Problem 1 and for $\mathrm{QSI}^\varepsilon_n$
-- statement:
--   For every constant $c>0$ there is a constant $C>0$, depending only on $c$, such that the following holds for every $n\ge2$, $0<\varepsilon<1/4$ and $0<\delta\le\frac12-c$. Every quantum algorithm that uses $m$ copies of each input state and solves Problem 1 with angle $\alpha=\frac12\arccos\sqrt{1-\varepsilon}$ with probability at least $1-\delta$ satisfies
--
--   $$
--   m\ge C\,\frac{\log(n/\delta)}{\log(1/\varepsilon)},
--   $$
--
--   and the same holds for every quantum algorithm that solves $\mathrm{QSI}^\varepsilon_n$ with error $\delta$, in every local dimension $d\ge2$. That is, $m=\Omega\bigl(\log(n/\delta)/\log(1/\varepsilon)\bigr)$ with the hidden constant depending only on $c$.
--
--   For constant $\varepsilon$ this matches the $O(\log(n/\delta))$ copies of Algorithm 3 (Theorems 4.3–4.4 and 1.3).
--
--   **Formalization Note** The $\Omega(\cdot)$ is made explicit as $\forall c>0\ \exists C>0$ before $n,\varepsilon,\delta,d,m$ and the algorithm; algorithms are published testers.
--
--   Differences from the source:
--   - encoding: m = Ω(log(n/δ)/log(1/ε)) with the constant depending only on c → ∀ c > 0, ∃ C > 0, ∀ n, ε, δ, m, d, T: m ≥ C log(n/δ)/log(1/ε); reason: the meaning of the Ω(·) with the stated dependence
--   - encoding: "every quantum algorithm ... must use ... copies of each input state" → every Tester n m 2 (resp. Tester n m d, d ≥ 2) solving the problem with error δ; reason: the published tester model represents every algorithm with m copies of each state
--   - encoding: indices $1,\dots,n$ → `Fin n`, label $i$ is the source's $i+1$; reason: Lean convention; same instances
-- source:
--   Shih-Han Hung, Ming-Hsien Tsai, STOC 2027 submission #321 (October 2026), Theorem 5.6, PDF/printed p.22, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/321.pdf

import Definitions.Def_QuantumStateIdentity321_Schur_Supplement_LowerBound

namespace QuantumStateIdentity321.Schur.Supplement

open Matrix

/-- Theorem 5.6, p.22: for every constant `c > 0` there is `C > 0`, depending only on `c`, such
that for every `n ≥ 2`, `0 < ε < 1/4` and `0 < δ ≤ 1/2 − c`, every tester that uses `m` copies of
each input state and solves Problem 1 with `α = ½ arccos √(1 − ε)` with probability at least
`1 − δ` has `m ≥ C log(n/δ)/log(1/ε)`; the same holds for every tester that solves `QSI^ε_n` with
error `δ`, in every local dimension `d ≥ 2`. That is, `m = Ω(log(n/δ)/log(1/ε))`. -/
theorem theorem_5_6 :
    ∀ c : ℝ, 0 < c → ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, 2 ≤ n → ∀ ε δ : ℝ, 0 < ε → ε < 1 / 4 → 0 < δ → δ ≤ 1 / 2 - c → ∀ m : ℕ,
        (∀ T : Tester n m 2, SolvesProblem1 T (problem1Angle ε) δ →
          C * (Real.log (n / δ) / Real.log (1 / ε)) ≤ (m : ℝ)) ∧
        ∀ d : ℕ, 2 ≤ d → ∀ T : Tester n m d, SolvesQSI T ε δ →
          C * (Real.log (n / δ) / Real.log (1 / ε)) ≤ (m : ℝ) := by sorry

end QuantumStateIdentity321.Schur.Supplement
