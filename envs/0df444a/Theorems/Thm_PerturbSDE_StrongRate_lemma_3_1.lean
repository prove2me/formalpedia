-- Prove2me | Theorems.Thm_PerturbSDE_StrongRate_lemma_3_1
-- name    : PerturbSDE.StrongRate.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:08:52.737995+00:00
-- url     : https://prove2.me/theorems/59483464-d887-4328-9f2c-cc5c5dd978f1
-- title:
--   Lemma 3.1, p. 16 — ‖ψ'(v)‖ ≤ 3, ‖ψ'(v) − I‖ ≤ 3[1 ∧ ‖v‖]², ‖ψ''(v)(u,u)‖ ≤ 14[1 ∧ ‖v‖] for ψ(v) = v/(1+‖v‖²)
-- statement:
--   Let $d\in\mathbb N$ and let $\psi:\mathbb R^d\to\mathbb R^d$ be the taming map $\psi(v)=\dfrac{v}{1+\|v\|^2}$. Then for every $v\in\mathbb R^d$,
--   $$\|\psi'(v)\|_{L(\mathbb R^d)}\le3,\qquad\|\psi'(v)-I_{\mathbb R^d}\|_{L(\mathbb R^d)}\le3\,[1\wedge\|v\|]^2,\qquad\sup_{u\in\mathbb R^d,\ \|u\|\le1}\|\psi''(v)(u,u)\|\le14\,[1\wedge\|v\|].$$
--   Here $\|\cdot\|_{L(\mathbb R^d)}$ is the operator norm and $a\wedge b=\min(a,b)$.
--
--   These bounds are what makes the taming harmless for small increments: near $0$ the map $\psi$ agrees with the identity to second order, which yields the local-error estimates in the proof of Lemma 3.2.
--
--   **Formalization Note** $\psi'(v)$ is `fderiv ℝ ψ v` and $\psi''(v)(u,u)$ is `iteratedFDeriv ℝ 2 ψ v` applied to $(u,u)$; the supremum is written as a bound for every $u$ with $\|u\|\le1$.
-- source:
--   Hutzenthaler, Jentzen, arXiv:1401.0295v1, p. 16, Lemma 3.1

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_PerturbSDE_StrongRate_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace PerturbSDE.StrongRate

open EthierKurtz

/-- Hutzenthaler–Jentzen, arXiv:1401.0295v1, p. 16, Lemma 3.1: for `d ∈ ℕ` and
`ψ(v) = v / (1 + ‖v‖²)` on `ℝ^d`, for every `v ∈ ℝ^d`,
`‖ψ'(v)‖ ≤ 3`, `‖ψ'(v) − I‖ ≤ 3 [1 ∧ ‖v‖]²` (operator norms) and
`sup_{‖u‖ ≤ 1} ‖ψ''(v)(u, u)‖ ≤ 14 [1 ∧ ‖v‖]`. The second derivative is
`iteratedFDeriv ℝ 2 ψ v` applied to `(u, u)`. -/
theorem lemma_3_1 {d : ℕ} (hd : 1 ≤ d) (v : SDEState d) :
    ‖fderiv ℝ (tame (d := d)) v‖ ≤ 3 ∧
    ‖fderiv ℝ (tame (d := d)) v - ContinuousLinearMap.id ℝ (SDEState d)‖ ≤
      3 * (min 1 ‖v‖) ^ 2 ∧
    ∀ u : SDEState d, ‖u‖ ≤ 1 →
      ‖iteratedFDeriv ℝ 2 (tame (d := d)) v ![u, u]‖ ≤ 14 * min 1 ‖v‖ := by sorry

end PerturbSDE.StrongRate
