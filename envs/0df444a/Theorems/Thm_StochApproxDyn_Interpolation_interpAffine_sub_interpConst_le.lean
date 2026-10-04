-- Prove2me | Theorems.Thm_StochApproxDyn_Interpolation_interpAffine_sub_interpConst_le
-- name    : StochApproxDyn.Interpolation.interpAffine_sub_interpConst_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T07:09:11.450484+00:00
-- url     : https://prove2.me/theorems/4e9a71c0-bec3-4d49-a120-440ceca839f1
-- title:
--   Proposition 4.1, proof, p. 13 — the affine and piecewise constant interpolations differ by at most 2Δ(t − 1, T + 1) + K sup γ̄
-- statement:
--   Let $F:\mathbb R^d\to\mathbb R^d$ be continuous, let the step sizes satisfy $\gamma_n\ge0$, $\sum_n\gamma_n=\infty$, $\gamma_n\to0$, and let $\{x_n\}$ follow the scheme $x_{n+1}-x_n=\gamma_{n+1}(F(x_n)+U_{n+1})$. Suppose $\|F(x_n)\|\le K$ for all $n$. Then there is $t_0\ge1$ such that for all $t\ge t_0$ and all $T>0$,
--   $$\sup_{t\le u\le t+T}\|X(u)-\overline X(u)\|\le2\Delta(t-1,T+1)+\sup_{t\le u\le t+T}K\bar\gamma(u).$$
--
--   In the proof of Proposition 4.1 this estimate shows that $X-\overline X\to0$ uniformly on windows of length $T$ once A1 holds, so that $F(\overline X)$ may be replaced by $F(X)$ in Eq. (9).
--
--   **Formalization Note** "For $t$ large enough" is the existential threshold $t_0$, chosen independently of $T$; $t_0\ge1$ makes $\Delta(t-1,\cdot)$ a quantity on $\mathbb R_+$. The bound $K$ is a hypothesis on the iterates; in the paper it comes from A2 and the continuity of $F$ (A2′ also yields it). Both suprema are real suprema over bounded nonempty sets: $\bar\gamma$ takes finitely many values on $[t,t+T]$.
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), p. 13, proof of Proposition 4.1 (display following "Thus")

import Mathlib
import Definitions.Def_StochApproxDyn_Interpolation_Scheme

open scoped NNReal Topology
open Filter

namespace StochApproxDyn.Interpolation

/-- Benaïm 1999, proof of Proposition 4.1, p. 13: if `‖F(x_n)‖ ≤ K` for all `n`, then for all `t`
large enough (with `t ≥ 1`) and every `T > 0`,
`sup_{t≤u≤t+T} ‖X(u) − X̄(u)‖ ≤ 2Δ(t − 1, T + 1) + sup_{t≤u≤t+T} K γ̄(u)`.
The threshold does not depend on `T`. -/
theorem interpAffine_sub_interpConst_le {d : ℕ}
    (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hF : Continuous F)
    (γ : ℕ → ℝ) (hγ : IsStepSizeSeq γ) (x U : ℕ → EuclideanSpace ℝ (Fin d))
    (hx : SatisfiesScheme F γ x U) (K : ℝ) (hK : ∀ n : ℕ, ‖F (x n)‖ ≤ K) :
    ∃ t₀ : ℝ, 1 ≤ t₀ ∧ ∀ t : ℝ, t₀ ≤ t → ∀ T : ℝ, 0 < T → ∀ u ∈ Set.Icc t (t + T),
      ‖interpAffine γ x u - interpConst γ x u‖ ≤
        2 * Delta γ U (t - 1) (T + 1) +
          sSup ((fun v => K * stepInterp γ v) '' Set.Icc t (t + T)) := by sorry

end StochApproxDyn.Interpolation
