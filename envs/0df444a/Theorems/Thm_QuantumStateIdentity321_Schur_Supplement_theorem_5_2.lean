-- Prove2me | Theorems.Thm_QuantumStateIdentity321_Schur_Supplement_theorem_5_2
-- name    : QuantumStateIdentity321.Schur.Supplement.theorem_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:01:10.895458+00:00
-- url     : https://prove2.me/theorems/b5b9cf1f-af61-4bc0-ae4f-078e77cdb403
-- title:
--   Theorem 5.2 — any algorithm for Problem 1 (hence for $\mathrm{QSI}^\varepsilon_n$) with error $\delta<1/2$ uses $m\ge\log(1/(4\delta(1-\delta)))/\log(1/\varepsilon)$ copies
-- statement:
--   Let $n\ge2$, $\varepsilon\in(0,1/2)$, $0<\delta<1/2$, and $\alpha=\frac12\arccos\sqrt{1-\varepsilon}$. Every quantum algorithm that uses $m$ copies of each input state and solves Problem 1 with angle $\alpha$ with probability at least $1-\delta$ (on every yes and every no input) satisfies
--
--   $$
--   m\ge\frac{\log\bigl(1/(4\delta(1-\delta))\bigr)}{\log(1/\varepsilon)}\qquad\text{and in particular}\qquad m\ge\frac{\log(1/(4\delta))}{\log(1/\varepsilon)} .
--   $$
--
--   The same two bounds hold for every quantum algorithm that solves $\mathrm{QSI}^\varepsilon_n$ with error $\delta$, in every local dimension $d\ge2$.
--
--   This is the $n$-independent half of the lower bound of Theorem 5.6.
--
--   **Formalization Note** An algorithm using $m$ copies of each input state is a published `Tester n m d` (qubits, $d=2$, for Problem 1).
--
--   Differences from the source:
--   - encoding: "any quantum algorithm ... must use at least ... copies of each input state" → every Tester n m 2 (resp. Tester n m d, d ≥ 2) solving the problem with error δ has m ≥ the bound; reason: the published tester model represents every algorithm with m copies of each state
--   - encoding: QSI^ε_n with ε ∈ [0, 1/2) → ε ∈ (0, 1/2); reason: at ε = 0 the bound has log(1/ε) = ∞ and is not a number; no instance with a meaningful bound is excluded
--   - encoding: indices $1,\dots,n$ → `Fin n`, label $i$ is the source's $i+1$; reason: Lean convention; same instances
-- source:
--   Shih-Han Hung, Ming-Hsien Tsai, STOC 2027 submission #321 (October 2026), Theorem 5.2, PDF/printed p.19, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/321.pdf

import Definitions.Def_QuantumStateIdentity321_Schur_Supplement_LowerBound

namespace QuantumStateIdentity321.Schur.Supplement

open Matrix

/-- Theorem 5.2, p.19: for `n ≥ 2`, `ε ∈ (0, 1/2)` and `0 < δ < 1/2`, every tester that uses `m`
copies of each input state and solves Problem 1 with `α = ½ arccos √(1 − ε)` with probability at
least `1 − δ` has `m ≥ log(1/(4δ(1−δ)))/log(1/ε)`, and in particular `m ≥ log(1/(4δ))/log(1/ε)`;
the same two bounds hold for every tester that solves `QSI^ε_n` with error `δ`, in every local
dimension `d ≥ 2`. -/
theorem theorem_5_2 (n : ℕ) (hn : 2 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) (m : ℕ) :
    (∀ T : Tester n m 2, SolvesProblem1 T (problem1Angle ε) δ →
        Real.log (1 / (4 * δ * (1 - δ))) / Real.log (1 / ε) ≤ (m : ℝ) ∧
        Real.log (1 / (4 * δ)) / Real.log (1 / ε) ≤ (m : ℝ)) ∧
      ∀ d : ℕ, 2 ≤ d → ∀ T : Tester n m d, SolvesQSI T ε δ →
        Real.log (1 / (4 * δ * (1 - δ))) / Real.log (1 / ε) ≤ (m : ℝ) ∧
        Real.log (1 / (4 * δ)) / Real.log (1 / ε) ≤ (m : ℝ) := by sorry

end QuantumStateIdentity321.Schur.Supplement
