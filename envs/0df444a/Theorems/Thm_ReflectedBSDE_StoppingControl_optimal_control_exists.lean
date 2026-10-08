-- Prove2me | Theorems.Thm_ReflectedBSDE_StoppingControl_optimal_control_exists
-- name    : ReflectedBSDE.StoppingControl.optimal_control_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:14:24.570131+00:00
-- url     : https://prove2.me/theorems/e42a1692-cddf-42da-b9d8-093120bf2595
-- title:
--   §7, p. 725 — an optimal control $(\beta^*,\gamma^*)\in\mathcal A$ attains the conjugate representation along $(Y,Z)$
-- statement:
--   Let the data $(\xi,f,S)$ satisfy (i)–(iv) and $S_T\le\xi$, with $f(\omega,t,\cdot,\cdot)$ concave for each $(\omega,t)$, and let $(Y,Z,K)$ be the solution of the reflected BSDE with coefficient $f$. Then there exists $(\beta^*,\gamma^*)\in\mathcal A$ such that
--   $$f(t,Y_t,Z_t)=F(t,\beta^*_t,\gamma^*_t)+\beta^*_tY_t+\langle\gamma^*_t,Z_t\rangle\qquad dt\times dP\text{ a.e.}$$
--   Hence $(Y,Z,K)$ is the solution $(Y^{\beta^*,\gamma^*},Z^{\beta^*,\gamma^*},K^{\beta^*,\gamma^*})$ of the reflected BSDE with the affine coefficient $f^{\beta^*,\gamma^*}$.
--
--   Together with the comparison theorem this gives $Y_t=\operatorname*{ess\,inf}_{(\beta,\gamma)\in\mathcal A}Y^{\beta,\gamma}_t$, with the infimum attained at $(\beta^*,\gamma^*)$.
--
--   **Formalization Note** The $dt\times dP$-a.e. identity is stated as: for a.e. $\omega$, for Lebesgue-a.e. $t\in[0,T]$, $F(t,\beta^*_t,\gamma^*_t)<\infty$ and the identity holds. The second conclusion is stated for every solution $(Y^*,Z^*,K^*)$ of the reflected BSDE with coefficient $f^{\beta^*,\gamma^*}$: a.s. $Y_t=Y^*_t$ and $K_t=K^*_t$ for all $t\in[0,T]$, and $Z=Z^*$ $dt\times dP$-a.e.
-- source:
--   El Karoui, Kapoudjian, Pardoux, Peng & Quenez, Reflected solutions of backward SDE's, and related obstacle problems for PDE's, Ann. Probab. 25(2) (1997), p. 725, §7 (displays preceding Theorem 7.2), https://doi.org/10.1214/aop/1024404416

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_MultiperiodRisk_Bellman_EssInf
import Definitions.Def_ReflectedBSDE_StoppingControl_Setting
import Definitions.Def_ReflectedBSDE_StoppingControl_Control

namespace ReflectedBSDE.StoppingControl

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

/-- §7, p. 725 (display after the definition of `𝒜`). With `f` concave in `(y, z)` and
`(Y, Z, K)` the solution of the reflected BSDE with coefficient `f`, there is
`(β*, γ*) ∈ 𝒜` with `f(t, Y_t, Z_t) = F(t, β*_t, γ*_t) + β*_t Y_t + ⟨γ*_t, Z_t⟩` `dt × dP`-a.e.;
hence every solution `(Y*, Z*, K*)` of the reflected BSDE with the affine coefficient
`f^{β*,γ*}` coincides with `(Y, Z, K)`: `Y = Y*`, `K = K*` on `[0, T]` a.s. and `Z = Z*`
`dt × dP`-a.e. -/
theorem optimal_control_exists {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → Fin d → ℝ} (hB : Peng1990.SMP.IsStdBrownian P B)
    (T : ℝ≥0) (ξ : Ω → ℝ) (f : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ) (S : ℝ≥0 → Ω → ℝ)
    (hdata : StandingData (augFiltration hB) P T ξ f S)
    (hLip : ∃ K : ℝ, IsLipschitzCoeff P T f K)
    (hconc : ∀ ω, ∀ t ≤ T, ConcaveOn ℝ Set.univ (fun p : ℝ × (Fin d → ℝ) => f t ω p.1 p.2))
    (Y : ℝ≥0 → Ω → ℝ) (Z : ℝ≥0 → Ω → Fin d → ℝ) (K : ℝ≥0 → Ω → ℝ)
    (hsol : IsRBSDESolution (augFiltration hB) P T B ξ f S Y Z K) :
    ∃ c ∈ admissible (augFiltration hB) P T f,
      (∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
        conj f ω s.toNNReal (c.1 s.toNNReal ω) (c.2 s.toNNReal ω) < ⊤ ∧
        f s.toNNReal ω (Y s.toNNReal ω) (Z s.toNNReal ω)
          = (conj f ω s.toNNReal (c.1 s.toNNReal ω) (c.2 s.toNNReal ω)).toReal
            + c.1 s.toNNReal ω * Y s.toNNReal ω + dot (c.2 s.toNNReal ω) (Z s.toNNReal ω)) ∧
      ∀ (Y' : ℝ≥0 → Ω → ℝ) (Z' : ℝ≥0 → Ω → Fin d → ℝ) (K' : ℝ≥0 → Ω → ℝ),
        IsRBSDESolution (augFiltration hB) P T B ξ (affineCoeff f c) S Y' Z' K' →
          (∀ᵐ ω ∂P, ∀ t ≤ T, Y t ω = Y' t ω ∧ K t ω = K' t ω) ∧
          ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
            Z s.toNNReal ω = Z' s.toNNReal ω := by sorry

end ReflectedBSDE.StoppingControl
