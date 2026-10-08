-- Prove2me | Theorems.Thm_RegMCBSDE_Simulation_eq_34_theta_infty_formula
-- name    : RegMCBSDE.Simulation.eq_34_theta_infty_formula
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:38:49.474977+00:00
-- url     : https://prove2.me/theorems/31b7a9d4-dbb7-41cb-bdd8-c2d3adc71717
-- title:
--   Proof of Theorem 3, Step 3, Eq. (34) — θ^{∞,I}_k = E(v_k[α^{I,I}_{0,k+1}·p_{0,k+1} + h f_k(α^{∞,I}_k)])
-- statement:
--   Let the model satisfy (H1)–(H2), the data be admissible and the bases orthonormal, let $C_fh<1$, $I\ge1$, and let $(\alpha^{i,I})$ be the projection–Picard scheme. Fix $0\le k\le N-1$ and let $\alpha^{\infty,I}_{0,k}$ be the coefficient vector of the fixed point $Y^{N,\infty,I}_{t_k}$ of (13),
--   $$Y^{N,\infty,I}_{t_k}=\mathcal P_{p_{0,k}}\big(Y^{N,I,I}_{t_{k+1}}+hf(t_k,S^N_{t_k},Y^{N,\infty,I}_{t_k},Z^{N,I,I}_{t_k})\big),$$
--   that is, $\alpha^{\infty,I}_{0,k}$ minimizes $a\mapsto\mathbb E\big(Y^{N,I,I}_{t_{k+1}}+hf(t_k,S^N_{t_k},\alpha^{\infty,I}_{0,k}\cdot p_{0,k},Z^{N,I,I}_{t_k})-a\cdot p_{0,k}\big)^2$; set $\alpha^{\infty,I}_{l,k}=\alpha^{I,I}_{l,k}$ for $l\ge1$ and let $\theta^{\infty,I}_k$ be its rescaling. Then
--   $$\theta^{\infty,I}_k=\mathbb E\big(v_k\,[\alpha^{I,I}_{0,k+1}\cdot p_{0,k+1}+hf_k(\alpha^{\infty,I}_k)]\big), \qquad (34)$$
--   componentwise, all the integrands being integrable.
--
--   Formula (34) expresses the projection coefficients as an expectation of the same form as the empirical regression, which is what makes the comparison with the simulation-based coefficients possible in the proof of Theorem 3.
--
--   **Formalization Note** The paper writes $\alpha^{I,I}_{0,k+1}\cdot p_{0,k+1}$ for $Y^{N,I,I}_{t_{k+1}}$; at $k=N-1$ this is $\Phi^N(P^N_{t_N})$. The fixed point of (13) is taken as a hypothesis on $\alpha^{\infty,I}_{0,k}$, stated through the minimization that defines the $\mathbf L_2$ projection. $I\ge1$ is needed so that $\alpha^{I,I}_k$ comes from a regression step ($\alpha^{0,I}_k=0$).
-- source:
--   Gobet, Lemor and Warin, A regression-based Monte Carlo method to solve backward stochastic differential equations, arXiv:math/0508491v1, p. 20, Proof of Theorem 3, Step 3, Eq. (34)

import Mathlib
import Definitions.Def_RegMCBSDE_Simulation_Setting
import Definitions.Def_RegMCBSDE_Simulation_ProjectionScheme
import Definitions.Def_RegMCBSDE_Simulation_EmpiricalScheme

namespace RegMCBSDE.Simulation

open MeasureTheory ProbabilityTheory

/-- Proof of Theorem 3, Step 3, Eq. (34), p. 20: the expectation formula for `θ^{∞,I}_k`.
Let the bases be orthonormal, `I ≥ 1`, `C_f h < 1`, `α^{i,I}` a projection–Picard scheme and
`k ≤ N-1`. Let `α^{∞,I}_{0,k}` be the coefficient vector of the fixed point `Y^{N,∞,I}_{t_k}` of (13):
`α^{∞,I}_{0,k}` minimizes `a ↦ 𝔼(Y^{N,I,I}_{t_{k+1}} + h f(t_k, S^N_{t_k}, α^{∞,I}_{0,k}·p_{0,k}, Z^{N,I,I}_{t_k}) - a·p_{0,k})²`,
i.e. `Y^{N,∞,I}_{t_k} = 𝒫_{p_{0,k}}(Y^{N,I,I}_{t_{k+1}} + h f(t_k, S^N_{t_k}, Y^{N,∞,I}_{t_k}, Z^{N,I,I}_{t_k}))`;
and put `α^{∞,I}_{l,k} = α^{I,I}_{l,k}` for `l ≥ 1`. Then, componentwise,
`θ^{∞,I}_k = 𝔼(v_k [Y^{N,I,I}_{t_{k+1}} + h f_k(α^{∞,I}_k)])`, the integrands being integrable.
Here `Y^{N,I,I}_{t_{k+1}} = α^{I,I}_{0,k+1}·p_{0,k+1}` (the paper's notation) for `k+1 < N`, and
`Φ^N(P^N_{t_N})` for `k = N-1`. -/
theorem eq_34_theta_infty_formula {d q : ℕ} (m : Model d q) (hm : m.Standing) {d' : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : RefData d q d' Ω) (B : Basis q d') (hD : D.IsAdmissible m P) (hB : B.IsOrthonormal D P)
    (hh : m.Cf * m.h D.N < 1) (I : ℕ) (hI : 1 ≤ I) (α : ℕ → (k : ℕ) → Coeff B k)
    (hα : IsProjectionScheme m D B P I α) (k : ℕ) (hk : k < D.N) (αinf0 : Fin (B.n 0 k) → ℝ) :
    let αinf : Coeff B k := @Fin.cases q (fun l => Fin (B.n l k) → ℝ) αinf0 (fun j => α I k j.succ)
    IsMinOn (fun a : Fin (B.n 0 k) → ℝ => ∫⁻ ω, ENNReal.ofReal
        ((projResp D B (α I) k ω + m.h D.N * drv m D B k αinf ω - a ⬝ᵥ B.p 0 k (D.PN k ω)) ^ 2) ∂P)
      Set.univ αinf0 →
    ∀ x : Idx B k,
      Integrable (fun ω => vvec m D B k ω x * (projResp D B (α I) k ω + m.h D.N * drv m D B k αinf ω)) P ∧
      theta m D B αinf x =
        ∫ ω, vvec m D B k ω x * (projResp D B (α I) k ω + m.h D.N * drv m D B k αinf ω) ∂P := by sorry

end RegMCBSDE.Simulation
