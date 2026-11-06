-- Prove2me | Theorems.Thm_SKWeakPoincare_theorem_2_2
-- name    : SKWeakPoincare.theorem_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:41:09.552539+00:00
-- url     : https://prove2.me/theorems/8eba732d-c464-48ba-ac53-df2ecccc23cb
-- title:
--   Theorem 2.2 — TAP residual bound: $\|R_{\mathrm{TAP}}(m(A,Y_t);A_{\mathrm{full}},Y_t,q_\beta(t))\|_2^2\le C_H\log n$ w.p. $1-n^{-H}$
-- statement:
--   Fix $0<\beta^*<1$ and $T>0$. For every $H>0$ there are $C_H,n_H>0$, depending only on $(\beta^*,T,H)$, such that for every $n\ge n_H$, every $\beta\in[0,\beta^*]$ and every $t\in[0,T]$,
--   $$
--   P^{\mathrm{pl,aug}}_{n,\beta}\Big\{\big\|R_{\mathrm{TAP}}\big(m(A,Y_t);A_{\mathrm{full}},Y_t,q_\beta(t)\big)\big\|_2^2>C_H\log n\Big\}\le n^{-H}.
--   $$
--   Here $P^{\mathrm{pl,aug}}_{n,\beta}$ is the planted augmented law (Definition 3.2), $m(A,Y_t)$ is the exact posterior mean (the mean of the SK Gibbs law at inverse temperature $\beta$, matrix $A$ and field $Y_t$), $q_\beta(t)$ is the scalar fixed point (10), and
--   $$
--   R_{\mathrm{TAP}}(u;A_{\mathrm{full}},y,q)=\operatorname{arctanh}(u)-y-\beta A_{\mathrm{full}}u+\beta^2(1-q)u .
--   $$
--
--   The exact posterior mean thus nearly solves the TAP stationarity equation, with an $O(\log n)$ squared residual. Through contiguity and local strong convexity of the TAP free energy this gives the Lipschitz property with cost functions (Lemma 2.1).
--
--   **Formalization Note** A sample of `plantedAugLaw β n` is $((W,X),(d,g))$, with $A=$ `plantedMatrix β W X`, $A_{\mathrm{full}}=A+\mathrm{diag}(d)$ and $Y_t=tX+\sqrt t\,g$. The posterior mean is `tapMean (tilt (gibbs (plantedDisorder β W X)) Y_t)`, where `plantedDisorder β W X` is $\beta A$ on the edges.
--
--   Differences from the source:
--   - encoding: sup over β ∈ [0,β*] and t ∈ [0,T] of the probability is ≤ n^{−H} → for every β ∈ [0,β*] and t ∈ [0,T] the probability is ≤ n^{−H}; reason: a supremum is ≤ c iff every term is
--   - encoding: the planted augmented law of (X, A, d, Y) with a Brownian path Y → plantedAugLaw β n on ((W, X), (d, g)) with Y_t = tX + √t g; reason: the event involves the path only at the fixed time t, and B_t has the law of √t g, independent of (X, W, d)
--   - encoding: q_β(t), the unique solution in [0,1] of (10) → every q with IsQFixed β t q; reason: the solution exists and is unique (Lemma 3.8), so the two statements are the same
--   - encoding: C_H, n_H > 0 → C : ℝ with 0 < C and nH : ℕ with 0 < nH; reason: n is a natural number
--   - encoding: arctanh(u) → Real.artanh; reason: Mathlib's artanh equals ½ log((1+u)/(1−u)) on (−1,1), and the posterior mean lies in (−1,1)ⁿ because the tilted Gibbs law has full support
--   - encoding: A_full, m(A, Y_t) and ‖·‖₂² → plantedMatrix β W X + Matrix.diagonal d, tapMean (tilt (gibbs (plantedDisorder β W X)) Y_t) and the sum of squared coordinates; reason: plantedDisorder β W X is βA on the edges, so its gibbs is μ_{β,A}; the zero-diagonal part plus diag(d) is A_full; the sum of squares is the squared Euclidean norm
-- source:
--   Hou–Liu–Yu, Simulated annealing and Weak Poincaré inequalities with inverse-polynomial accuracy for the Sherrington–Kirkpatrick model, arXiv:2610.09882, Theorem 2.2, p.11 (R_TAP p.11 and p.18; planted model Definition 3.2, p.15; q_β(t) eq. (10), p.17)

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_SKAnnealing_Sampling_tilt
import Definitions.Def_SKAnnealing_Sampling_tapHessian
import Definitions.Def_SKAnnealing_Sampling_plantedTilted
import Definitions.Def_SKWeakPoincare_tapResidual

open OAI.CriticalSK SKAnnealing.Sampling MeasureTheory

namespace SKWeakPoincare

/-- **Theorem 2.2 (TAP residual bound).**
Hou–Liu–Yu, arXiv:2610.09882, Theorem 2.2, p. 11 (planted model: Section 2.5.1, p. 11, and
Definition 3.2, p. 15; `R_TAP`: p. 11 and p. 18; `q_β(t)`: eq. (10), p. 17).

Fix `0 < β* < 1` and `T > 0`. For every `H > 0` there are `C_H, n_H > 0`, depending only on
`(β*, T, H)`, such that for `n ≥ n_H`, every `β ∈ [0, β*]` and every `t ∈ [0, T]`,
`P^{pl,aug}_{n,β}{‖R_TAP(m(A, Y_t); A_full, Y_t, q_β(t))‖₂² > C_H log n} ≤ n^{−H}`.

**Formalization Note.** A sample of `plantedAugLaw β n` is `((W, X), (d, g))`; `A = plantedMatrix β W X`
is the zero-diagonal part of `W + βXXᵀ/n`, `A_full = A + diag(d)`, `Y_t = tX + √t g` (the law of
`tX + B_t` at the fixed time `t`), and `m(A, Y_t)` is the mean of the Gibbs law at inverse
temperature `β`, matrix `A` and field `Y_t` (`plantedDisorder β W X` is `βA` on the edges). The
supremum over `(β, t)` is "for every `(β, t)`"; `q_β(t)` is every solution in `[0, 1]` of (10)
(unique by Lemma 3.8). -/
theorem theorem_2_2 (βs T : ℝ) (hβs0 : 0 < βs) (hβs1 : βs < 1) (hT : 0 < T) :
    ∀ H : ℝ, 0 < H → ∃ (C : ℝ) (nH : ℕ), 0 < C ∧ 0 < nH ∧ ∀ n : ℕ, nH ≤ n →
      ∀ β ∈ Set.Icc (0 : ℝ) βs, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q : ℝ, IsQFixed β t q →
        plantedAugLaw β n
            {w | C * Real.log n < ∑ i, (tapResidual β
                (plantedMatrix β w.1.1 w.1.2 + Matrix.diagonal w.2.1)
                (t • spinVec w.1.2 + Real.sqrt t • w.2.2) q
                (tapMean (tilt (gibbs (plantedDisorder β w.1.1 w.1.2))
                  (t • spinVec w.1.2 + Real.sqrt t • w.2.2))) i) ^ 2}
          ≤ ENNReal.ofReal ((n : ℝ) ^ (-H)) := by sorry

end SKWeakPoincare
