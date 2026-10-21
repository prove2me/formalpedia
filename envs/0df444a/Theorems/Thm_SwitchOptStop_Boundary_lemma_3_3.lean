-- Prove2me | Theorems.Thm_SwitchOptStop_Boundary_lemma_3_3
-- name    : SwitchOptStop.Boundary.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:06:50.157522+00:00
-- url     : https://prove2.me/theorems/219e94c2-0104-468a-8f7a-39b037e02938
-- title:
--   Lemma 3.3, p. 8 — if τ_{D^{N0}} is a.s. finite with (3.6) and ∂D is Green regular, then τ_D is optimal for (2.1)
-- statement:
--   Assume the setting of the mission with Assumptions 2.1, 2.2, 2.3 and $\underline H<0$. Suppose there is $N_0>0$ such that, for every $(\iota,x)\in M\times(0,\infty)^2$, the first entry time $\tau_{D^{N_0}}$ is finite $\mathsf P_{\iota,x}$-a.s. and
--   $$
--   \mathsf E_{\iota,x}\int_0^{\tau_{D^{N_0}}}e^{-\Lambda_t}|H(\alpha_t,X_t)|\,dt<\infty. \tag{3.6}
--   $$
--   Suppose moreover that $\partial D$ is Green regular. Then $\tau_D$ is an optimal stopping time for (2.1):
--   $$
--   V(\iota,x)=\mathsf E_{\iota,x}\int_0^{\tau_D}e^{-\Lambda_t}H(\alpha_t,X_t)\,dt\qquad\text{for all }\iota,\ x\in(0,\infty)^2.
--   $$
--
--   This is the criterion through which Theorem 3.8 is proved.
--
--   **Formalization Note** Green regularity is the predicate `IsGreenRegular` (convergence $\tau_D\to0$ in probability as the starting point approaches the boundary of $C_\iota$ from inside). The conclusion includes that $\tau_D$ is a stopping time of the augmented filtration of $(\alpha,X)$, and the expectation is the `EReal` cost.
-- source:
--   Ernst & Mei, Exact optimal stopping for multidimensional linear switching diffusions, arXiv:2107.14441v1, p. 8, Lemma 3.3, (3.6)

import Mathlib
import Definitions.Def_SwitchOptStop_Boundary_Value

namespace SwitchOptStop.Boundary

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

/-- Lemma 3.3 (p. 8): if for some `N₀ > 0` the entry time of `D^{N₀}` is finite a.s. and (3.6)
holds from every starting point, and `∂D` is Green regular, then `τ_D` is an optimal stopping time
for (2.1). -/
theorem lemma_3_3 (m : Model) (hQ : IsGenerator m) (h21 : Assumption21 m) (h22 : Assumption22 m)
    (hH : Hlow m < 0) {Ω : Type} [MeasurableSpace Ω] (S : Setting Ω) (hS : IsSetting m S)
    (h23 : Assumption23 S)
    (hN0 : ∃ N0 : ℝ, 0 < N0 ∧ ∀ ι : Fin 2, ∀ x ∈ openQuadrant,
      (∀ᵐ ω ∂(Pι S ι), entryTime S x (stopSetN m S N0 0) ω < ⊤) ∧
      (∫⁻ ω, ∫⁻ t in {t : ℝ | 0 ≤ t ∧
          ((t.toNNReal : ℝ≥0) : WithTop ℝ≥0) < entryTime S x (stopSetN m S N0 0) ω},
          ENNReal.ofReal (Real.exp (-Λ m S t ω) *
            |m.H (S.α t.toNNReal ω) (S.X x t.toNNReal ω)|) ∂volume ∂(Pι S ι)) < ⊤)
    (hG : IsGreenRegular m S) :
    ∀ ι : Fin 2, ∀ x ∈ openQuadrant,
      IsStoppingTime (S.𝔾 x) (entryTime S x (stopSet m S)) ∧
      valueE m S ι x = costJ (Pι S ι) (costV m S x) (entryTime S x (stopSet m S)) := by sorry

end SwitchOptStop.Boundary
