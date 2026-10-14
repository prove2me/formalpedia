-- Prove2me | Theorems.Thm_QAlgorithms_Arunachalam_avg_agnostic_lower_bound
-- name    : QAlgorithms.Arunachalam.avg_agnostic_lower_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:56:09.064486+00:00
-- url     : https://prove2.me/theorems/25fe0f38-9c28-4d9b-afdd-87f97b4ac519
-- title:
--   ε-average agnostic learners need (d/ε²)(1/62 − log(2d+2)/(4d)) samples
-- statement:
--   Let $C\subseteq\{c:\{0,1\}^n\to\{0,1\}\}$ be a concept class of VC dimension $d\ge1$, and let $\varepsilon\in(0,1/10]$. An $\varepsilon$-average agnostic learner for $C$ using $T$ samples is a randomized map from $T$ i.i.d. samples $(X,Y)\sim D^T$ to a hypothesis $h_{XY}$ such that, for every distribution $D$ on $\{0,1\}^{n+1}$,
--
--   $$
--   \mathbb E_{(X,Y)\sim D^T}\big[\mathrm{err}_D(h_{XY})\big]-\mathrm{opt}_D(C)\le\varepsilon,
--   $$
--
--   where $\mathrm{err}_D(h)=\Pr_{(x,b)\sim D}[h(x)\ne b]$ and $\mathrm{opt}_D(C)=\min_{c\in C}\mathrm{err}_D(c)$. Then every $\varepsilon$-average agnostic learner for $C$ satisfies
--
--   $$
--   T\ \ge\ \frac{d}{\varepsilon^2}\left(\frac1{62}-\frac{\log_2(2d+2)}{4d}\right).
--   $$
--
--   This is the explicit-constant (minimax) form of the agnostic lower bound, comparable to Audibert's $T\ge d/(36\varepsilon^2)$.
--
--   **Formalization Note** The source's "there exists a distribution for which every learner" refers to the proof's hard distribution, which is random; the learner is required to be $\varepsilon$-good for every unknown $D$, as in the definition. $d\ge1$ is assumed because the bound divides by $d$. Hypotheses are not required to lie in $C$ (the definition on p.166 does not require it); on the proof's distributions, supported on a shattered set, this makes no difference.
-- source:
--   Srinivasan Arunachalam, Quantum Algorithms and Learning Theory — Part II, 2018 thesis, ILLC DS-2018-08, PDF p. 167, Theorem 7.4.5. https://ir.cwi.nl/pub/27536/Thesis_S_Arunachalam

import Definitions.Def_QAlgorithms_Defs_Learning
set_option autoImplicit false

namespace QAlgorithms.Arunachalam

open QAlgorithms.Learning






/-- Arunachalam p.166–168, Theorem 7.4.5: for a concept class `C` with `VC-dim(C) = d` and every
`ε ∈ (0, 1/10]`, every `ε`-average agnostic learner for `C` (using `T` samples from `AEX(D)` and
satisfying `E_{(X,Y)∼D^T}[err_D(h_{XY})] − opt_D(C) ≤ ε` for every distribution `D`) has
`T ≥ (d/ε²) · (1/62 − log(2d + 2)/(4d))`, `log` base 2.

The source's "there exists a distribution for which every learner …" is the proof's random
hard distribution `D_a`; a learner is required to be `ε`-good for every unknown `D`, as the
definition on p.166 says. `d ≥ 1` is assumed because the bound divides by `d` (trap 14). -/
theorem avg_agnostic_lower_bound (n : ℕ) (C : Finset (Qubits n → Bool)) (d : ℕ)
    (hd : vcDimClass C = d) (hd1 : 1 ≤ d) (ε : ℝ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 10) (T : ℕ)
    (L : (Fin T → Qubits n × Bool) → PMF (Qubits n → Bool))
    (hL : IsAvgAgnosticLearner C ε T L) :
    (d : ℝ) / ε ^ 2 * (1 / 62 - Real.logb 2 (2 * d + 2) / (4 * d)) ≤ T := by
  sorry

end QAlgorithms.Arunachalam
