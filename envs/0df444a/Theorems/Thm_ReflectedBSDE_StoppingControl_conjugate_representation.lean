-- Prove2me | Theorems.Thm_ReflectedBSDE_StoppingControl_conjugate_representation
-- name    : ReflectedBSDE.StoppingControl.conjugate_representation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:13:19.062986+00:00
-- url     : https://prove2.me/theorems/0dbc9cf4-5e46-438c-b9e2-2f04d24ccd08
-- title:
--   §7, p. 724 — a concave Lipschitz coefficient is the minimum of its affine minorants $F(t,\beta,\gamma)+\beta y+\langle\gamma,z\rangle$
-- statement:
--   Let $f(\omega,t,y,z)$ be a coefficient such that, for each fixed $(\omega,t)$ with $t\in[0,T]$, $(y,z)\mapsto f(\omega,t,y,z)$ is concave on $\mathbb R\times\mathbb R^d$, and which satisfies the Lipschitz condition (iii). Let $F$ be its conjugate function and $D^F_t(\omega)=\{(\beta,\gamma):F(\omega,t,\beta,\gamma)<\infty\}$. Then for every $(\omega,t)$ and every $(y,z)$,
--   $$f(t,y,z)=\inf_{(\beta,\gamma)\in D^F_t}\big\{F(t,\beta,\gamma)+\beta y+\langle\gamma,z\rangle\big\},$$
--   the infimum is achieved, and the set $D^F_t$ is a.s. bounded.
--
--   This conjugacy is what turns the concave coefficient into a family of affine ones, indexed by the controls $(\beta,\gamma)$.
--
--   **Formalization Note** The infimum is stated as an attained minimum: every $(\beta,\gamma)\in D^F_t$ gives an upper bound, and some $(\beta,\gamma)\in D^F_t$ gives equality; $F$ is read as a real number on $D^F_t$, where it is finite. "A.s. bounded" is read as: for a.e. $\omega$, $D^F_t(\omega)$ is bounded for every $t\in[0,T]$. Only concavity and (iii) are assumed, since the display is a statement of convex analysis about each $f(\omega,t,\cdot,\cdot)$.
-- source:
--   El Karoui, Kapoudjian, Pardoux, Peng & Quenez, Reflected solutions of backward SDE's, and related obstacle problems for PDE's, Ann. Probab. 25(2) (1997), p. 724, §7 (display following the definition of F and D^F_t), https://doi.org/10.1214/aop/1024404416

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_MultiperiodRisk_Bellman_EssInf
import Definitions.Def_ReflectedBSDE_StoppingControl_Setting
import Definitions.Def_ReflectedBSDE_StoppingControl_Control

namespace ReflectedBSDE.StoppingControl

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

/-- §7, p. 724 (conjugacy display). If `f(ω, t, ·, ·)` is concave on `ℝ × ℝ^d` for each
`(ω, t)` and `f` satisfies the Lipschitz condition (iii), then for each `(ω, t)` and `(y, z)`,
`f(t, y, z) = inf_{(β, γ) ∈ D^F_t} {F(t, β, γ) + βy + ⟨γ, z⟩}` with the infimum achieved, and
a.s. the set `D^F_t` is bounded (for every `t ∈ [0, T]`). -/
theorem conjugate_representation {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    (T : ℝ≥0) (f : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ)
    (hconc : ∀ ω, ∀ t ≤ T, ConcaveOn ℝ Set.univ (fun p : ℝ × (Fin d → ℝ) => f t ω p.1 p.2))
    (hLip : ∃ K : ℝ, IsLipschitzCoeff P T f K) :
    (∀ ω, ∀ t ≤ T, ∀ (y : ℝ) (z : Fin d → ℝ),
      (∀ p ∈ conjDomain f ω t, f t ω y z ≤ (conj f ω t p.1 p.2).toReal + p.1 * y + dot p.2 z) ∧
      ∃ p ∈ conjDomain f ω t, f t ω y z = (conj f ω t p.1 p.2).toReal + p.1 * y + dot p.2 z) ∧
    ∀ᵐ ω ∂P, ∀ t ≤ T, Bornology.IsBounded (conjDomain f ω t) := by sorry

end ReflectedBSDE.StoppingControl
