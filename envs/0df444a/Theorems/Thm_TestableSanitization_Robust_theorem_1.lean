-- Prove2me | Theorems.Thm_TestableSanitization_Robust_theorem_1
-- name    : TestableSanitization.Robust.theorem_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:54:46.040073+00:00
-- url     : https://prove2.me/theorems/b02dd057-d83e-4d49-9130-da0e428f2409
-- title:
--   Theorem 1 — $(\alpha,\eta,\eta)$-testable sanitization for every $\alpha>1$: $O(\log(1/\zeta)/\eta)$ samples, $O(m\log(m/\zeta)(1+\frac1{\alpha^2-1})^d)$ queries, $\tilde O(dq+d^2\log(1+\mu/r))$ time
-- statement:
--   There are universal constants $C>0$, $k\in\mathbb N$ and $c\in(0,1)$ such that the following holds. For every dimension $d\ge1$, every $\alpha>1$, $\eta,\zeta\in(0,1/2)$ and $\mu>0$ there is an algorithm — a pair $(P,E)$ of programs of the randomized oracle real RAM, $E$ deterministic, both with rational literals only — which receives the radius $r$ (with $d,\alpha,\eta,\zeta,\mu$) as input and is an **$(\alpha,\eta,\eta)$-testable sanitization algorithm with success probability $1-\zeta$** for all probability distributions $D$ on $\mathbb R^d$ with $\mathbb E_{x\sim D}\|x\|\le\mu$: for every $r>0$, every measurable classifier $f:\mathbb R^d\to\{\pm1\}$ and every such $D$,
--   - **(soundness)** the probability that $P$ accepts and the output $g^f$ (the program $E$ run on $P$'s final memory, with oracle $f$) fails to define a $\pm1$ value everywhere, or has $\Pr_{x\sim D}[f(x)\neq g^f(x)]>\eta$, or has $D(\partial g^f_r)>\eta$, is at most $\zeta$;
--   - **(completeness)** if $D(\partial f_{\alpha r})\le c\eta$, the probability that $P$ does not accept is at most $\zeta$;
--
--   and on every run, with $m_0=\log(1/\zeta)/\eta$ and $q_0=m_0\log(m_0/\zeta)(1+\frac1{\alpha^2-1})^d$, $P$ draws at most $C m_0+C$ samples, makes at most $Cq_0+C$ queries and takes at most
--   $$C\big(d\,q_0+d^2\log(1+\mu/r)\big)\log\big(2+d+1/\eta+1/\zeta\big)^k+C$$
--   steps. That is: sample complexity $m=O(\log(1/\zeta)/\eta)$, query complexity $q=O\big(m\log(m/\zeta)(1+\frac1{\alpha^2-1})^d\big)$, runtime $\tilde O(dq+d^2\log(1+\mu/r))$, with $\tilde O$ suppressing logarithmic factors in $d$, $1/\eta$, $1/\zeta$.
--
--   This is the paper's main algorithmic result: for any approximation ratio $\alpha>1$ a black-box classifier can be tested and, when accepted, replaced by a classifier with small boundary mass at radius $r$ and small distance to $f$, with a query cost that becomes polynomial for $\alpha\approx\sqrt{d/\log d}$ (Corollary 2).
--
--   **Formalization Note.** The machine, the two-program output and Definition 2 are the definitions `Machine` and `Sanitizer`. The runtime clause is stated as printed, with $\log(1+\mu/r)$; the paper's proof concludes $\tilde O(dq+d^2\log(2+\mu/r))$ (recorded as a finding of the mission).
--
--   Differences from the source:
--   - reading: 'There exists an algorithm A' (the paper names no computation model) that 'receives a radius r > 0, oracle access to f and sample access to D' → for each d, α, η, ζ, µ, a pair (P, E) of programs of the randomized oracle real RAM (Machine: rational literals, sqrt/exp/log, uniform and unit-ball draws at cost d, sample and query at cost d, no floor); P receives [d, α, η, ζ, µ, r] in fixed input cells; reason: a running-time statement needs a machine; the algorithm may depend on the theorem's parameters, and since literals are rational they are passed as inputs; r is an input as Definition 2 requires
--   - reading: the output ("Accept", g^f) with g^f : R^d → {±1} retaining oracle access to f → g^f = outputFn E d f M, the deterministic evaluation program E run with oracle f on P's final memory M; an E that does not return a ±1 value at some point counts as a soundness failure; reason: the output must be an algorithm with oracle access to f, not an arbitrary function
--   - reading: completeness 'If there exists universal constant c ∈ (0, 1) such that D(∂f_{αr}) ≤ cη' → one constant c ∈ (0, 1), quantified before d, α, η, ζ, µ, r, f and D; reason: the stronger of the two readings; the proof gives c = 1/20
--   - reading: O(·) and Õ(·) ('Õ suppresses logarithmic factors in d, 1/η, and 1/ζ'), with m in the query bound → O(X) as C·X + C and Õ(X) as C·X·log(2 + d + 1/η + 1/ζ)^k + C with universal C > 0 and k ∈ ℕ; m in the query bound is the expression log(1/ζ)/η; reason: explicit universal constants independent of every parameter; m = O(log(1/ζ)/η) is the paper's sample complexity
--   - reading: sample, query and runtime complexity of A → CostBounded: worst-case bounds for every r > 0, every classifier f, every value of the random streams and every number of steps, counted for the construction program P only; reason: complexity bounds are worst case; the paper's q counts the construction's m(K + 1) queries, and the cost of evaluating g^f is not bounded by Theorem 1
--   - encoding: probabilities over the samples and the algorithm's internal randomness; 'accepts with probability at least 1 − ζ' → the measure under streamLaw D (independent streams D^ℕ, Unif[0,1]^ℕ, U^ℕ) of the failure set, bounded by ζ; completeness as 'the set of runs that do not accept has measure ≤ ζ'; reason: failure probabilities as measures of failure sets (outer measures if not measurable, which only strengthens the bound)
--   - encoding: Pr_{x∼D}[f(x) ≠ g^f(x)] and D(∂g^f_r) → D-measures of the sets (outer measures; g^f need not be measurable); reason: no measurability hypothesis on the output is added
--   - encoding: E_{x∼D}‖x‖ ≤ µ, r, µ ∈ R+ → ∫⁻ x, ENNReal.ofReal ‖x‖ ∂D ≤ ENNReal.ofReal µ, 0 < µ, 0 < r; reason: lower Lebesgue integral of a nonnegative function; no integrability side condition
--   - encoding: the input space R^d (a dimension, d ≥ 1 as in Lemma 34) → d : ℕ with the hypothesis 1 ≤ d, points in EuclideanSpace ℝ (Fin d); reason: Lean convention for R^d with the Euclidean norm; excludes only the degenerate d = 0
--   - encoding: a Borel-measurable classifier f : R^d → {±1} (§2 standing assumption) → f : Pt d → ℝ with IsClassifier f (Measurable f and every value is 1 or -1); reason: the two labels ±1 as reals; same functions
-- source:
--   Cai, Mamali, Sotiraki, Yu, Zampetakis, Testable Sanitization via Boundary Geometry, STOC 2027 submission (manuscript sha256 bcf6434f…), p. 9 (PDF 11), Theorem 1 (restated p. 21, PDF 23; proved p. 27, PDF 29)

import Mathlib
import Definitions.Def_TestableSanitization_Robust_Boundary
import Definitions.Def_TestableSanitization_Robust_Sanitizer

open MeasureTheory

namespace TestableSanitization.Robust

theorem theorem_1 :
    ∃ (C : ℝ) (k : ℕ) (c : ℝ), 0 < C ∧ 0 < c ∧ c < 1 ∧
      ∀ (d : ℕ) (α η ζ μ : ℝ), 1 ≤ d → 1 < α → 0 < η → η < 1 / 2 → 0 < ζ → ζ < 1 / 2 → 0 < μ →
        ∃ P E : Program, Admissible P ∧ Admissible E ∧ Deterministic E ∧
          IsTestableSanitizer d α η η ζ c μ P E ∧
          CostBounded d α η ζ μ
            (fun _ => C * (Real.log (1 / ζ) / η) + C)
            (fun _ => C * ((Real.log (1 / ζ) / η) * Real.log ((Real.log (1 / ζ) / η) / ζ) *
                (1 + 1 / (α ^ 2 - 1)) ^ d) + C)
            (fun r => C * ((d : ℝ) * ((Real.log (1 / ζ) / η) *
                Real.log ((Real.log (1 / ζ) / η) / ζ) * (1 + 1 / (α ^ 2 - 1)) ^ d) +
                (d : ℝ) ^ 2 * Real.log (1 + μ / r)) *
                Real.log (2 + d + 1 / η + 1 / ζ) ^ k + C)
            P := by sorry

end TestableSanitization.Robust
