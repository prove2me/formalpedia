-- Prove2me | Theorems.Thm_QCopyMono_Supplement_theorem_3
-- name    : QCopyMono.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:21:47.915379+00:00
-- url     : https://prove2.me/theorems/399ba922-e4b3-4f9b-894d-56d582345865
-- title:
--   Theorem 3 — testing union-closedness or 2-monotonicity needs $\Omega(n^2)$ copies of $|\psi_f\rangle$ for every $0<\varepsilon\le1/256$
-- statement:
--   Let $|\psi_f\rangle=2^{-n/2}\sum_{x\in\{0,1\}^n}|x,f(x)\rangle$ be the quantum function state of $f:\{0,1\}^n\to\{0,1\}$. There is an absolute constant $c>0$ such that for every $n\ge2$ and every $0<\varepsilon\le1/256$:
--
--   1. every quantum algorithm that receives $t$ copies of $|\psi_f\rangle$ and decides, with success probability at least $2/3$, whether $f$ is union-closed or $\varepsilon$-far from union-closed uses $t\ge c\,n^2$ copies;
--   2. every quantum algorithm that receives $t$ copies of $|\psi_f\rangle$ and decides, with success probability at least $2/3$, whether $f$ is 2-monotone or $\varepsilon$-far from 2-monotone uses $t\ge c\,n^2$ copies.
--
--   $$
--   t\ \ge\ c\,n^{2}.
--   $$
--
--   Here a quantum algorithm on $t$ copies is an arbitrary two-outcome joint measurement on $|\psi_f\rangle^{\otimes t}$, and success probability $2/3$ means it accepts every function with the property with probability at least $2/3$ and every $\varepsilon$-far function with probability at most $1/3$.
--
--   These bounds show that the lower-bound construction for monotonicity transfers to other order-based properties of Boolean functions, with a quadratic dependence on $n$.
--
--   **Formalization Note** The algorithm is `IsPropTester P ε (1/3) t E` for $P$ union-closedness or 2-monotonicity (definition `QCopyMono.Supplement.IsPropTester`). One constant $c$ covers both properties and all $\varepsilon\in(0,1/256]$.
--
--   Differences from the source:
--   - reading: Ω(n^2) for every 0 < ε ≤ 1/256 → one absolute c > 0 with c·n² ≤ t for every n ≥ 2 and every ε ∈ (0, 1/256], for both properties; reason: at n = 1 every function is union-closed and 2-monotone, so a 0-copy tester exists and no bound c·n² > 0 can hold there; for each n ≥ 2 a 1/4-far function exists for each property, so a tester needs t ≥ 1 and the n ≥ 2 form is equivalent to the asymptotic Ω(n²)
--   - encoding: "any quantum algorithm … with success probability at least 2/3" → every effect E with IsPropTester P ε (1/3) t E; reason: every t-copy measurement followed by a yes/no decision induces such an effect; same model as the base mission's IsMonoTester
--   - encoding: dist(f, P) = min_{g∈P} dist(f, g) ≥ ε → ε ≤ dist(f, g) for every g ∈ P; reason: both classes are finite and nonempty (constant 0), so the minimum exists and the two conditions agree
-- source:
--   Naik, Quantum Copy Complexity of Testing Monotonicity and Other Properties, STOC 2027 submission (manuscript sha256 10fb417512cedc538a3dc512c3cd893806335ae8e073ebaf1deeeab8e5dac528), Theorem 3, p.4; definitions §5, p.29; proof §5, pp.29–32

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QCopyMono_IsMonoTester
import Definitions.Def_QCopyMono_Supplement_IsPropTester

namespace QCopyMono

namespace Supplement

open QAlgorithms

/-- Naik, *Quantum Copy Complexity of Testing Monotonicity and Other Properties*, STOC 2027
submission (manuscript sha256 10fb4175…dac528), Theorem 3 (Additional lower bounds), p.4
(proved in §5, pp.29–32): for every `0 < ε ≤ 1/256`, any quantum algorithm requires `Ω(n²)`
copies of `|ψ_f⟩` to decide, with success probability at least `2/3`, whether `f` is
union-closed or `ε`-far from union-closed. The same holds for testing 2-monotonicity.

**Formalization Note.** The `Ω(·)` is one absolute constant `c > 0` covering both properties,
chosen before `n`, `ε`, `t` and the algorithm; the bound is uniform in `ε ∈ (0, 1/256]`. An
algorithm on `t` copies is any two-outcome joint measurement, given by its accepting effect `E`;
"success probability at least `2/3`" is two-sided error `1/3` (`IsPropTester P ε (1/3) t E`).
The statement is for every `n ≥ 2`: at `n = 1` every function is union-closed and 2-monotone, so
a `0`-copy tester succeeds; for every `n ≥ 2` some function is `1/4`-far from each property, so a
tester needs `t ≥ 1`, and `∀ n ≥ 2` is the asymptotic `Ω(n²)` with no further threshold. -/
theorem theorem_3 :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 2 ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 256 →
      (∀ (t : ℕ) (E : Matrix (Fin t → X n) (Fin t → X n) ℂ),
        IsPropTester IsUnionClosed ε (1 / 3) t E → c * (n : ℝ) ^ 2 ≤ (t : ℝ)) ∧
      (∀ (t : ℕ) (E : Matrix (Fin t → X n) (Fin t → X n) ℂ),
        IsPropTester IsTwoMonotone ε (1 / 3) t E → c * (n : ℝ) ^ 2 ≤ (t : ℝ)) := by sorry

end Supplement

end QCopyMono
