-- Prove2me | Theorems.Thm_Peng1990_SMP_hamiltonian_expansion
-- name    : Peng1990.SMP.hamiltonian_expansion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T23:34:13.128461+00:00
-- url     : https://prove2.me/theorems/2d6f49f5-ff83-42a0-a77b-a33f02c02d28
-- title:
--   Eq. (14) — the cost expansion rewritten with the Hamiltonian is $\ge o(\varepsilon)$
-- statement:
--   Assume (3), let $(y,u)$ be optimal, and let $(p,K)$ be the first-order adjoint process of (13). Let $\tau$, $v$, $u^\varepsilon$ be as in Lemma 1 and $y_1=y_1^\varepsilon$ the solution of (5). Then
--   $$E\int_0^T\big(H(y(s),u^\varepsilon(s),p(s),K(s))-H(y(s),u(s),p(s),K(s))\big)ds+\tfrac12E\int_0^Ty_1^*(s)H_{xx}(y(s),u(s),p(s),K(s))y_1(s)\,ds+\tfrac12Ey_1^*(T)h_{xx}(y(T))y_1(T)\ \ge\ o(\varepsilon),$$
--   where $H(x,v,p,K)=l(x,v)+(p,g(x,v))+\sum_{j=1}^d(K_j,\sigma^j(x,v))$ and $H_{xx}$ is its Hessian in $x$. As in Lemma 2, the right side means some $r(\varepsilon)$ with $r(\varepsilon)/\varepsilon\to0$ as $\varepsilon\to0^+$.
--
--   This is (11) with the linear terms in $y_1$, $y_2$ replaced through the duality (13); only a quadratic form in $y_1$ remains.
--
--   **Formalization Note** The page writes $o^j(x,v)$ for $\sigma^j(x,v)$ in the definition of $H$ (misprint). The expectations are Bochner integrals; each integrand is integrable under the hypotheses ($p,K\in L^2$, fourth moments of $y_1$, boundedness of $v$).
-- source:
--   Peng, A General Stochastic Maximum Principle for Optimal Control Problems, SIAM J. Control Optim. 28(4), 1990, https://doi.org/10.1137/0328054, p. 972, (14) and the definition of $H$

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_Peng1990_SMP_ControlProblem
import Definitions.Def_Peng1990_SMP_Adjoint

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics
open scoped ENNReal NNReal Matrix

namespace Peng1990.SMP

theorem hamiltonian_expansion {Ω : Type*} [MeasurableSpace Ω] {n k d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (cp : ControlProblem n k d) (h3 : Assumption3 cp)
    (B : ℝ≥0 → Ω → Fin d → ℝ) (hB : IsStdBrownian P B)
    (y : ℝ≥0 → Ω → Fin n → ℝ) (u : ℝ≥0 → Ω → Fin k → ℝ)
    (hopt : IsOptimalPair cp (brownianFiltration hB) P B y u)
    (p : ℝ≥0 → Ω → Fin n → ℝ) (K : Fin d → ℝ≥0 → Ω → Fin n → ℝ)
    (hpK : RepresentsI cp (brownianFiltration hB) P B y u p K)
    (τ : ℝ≥0) (hτ : τ < cp.T) (v : Ω → Fin k → ℝ)
    (hv : Measurable[brownianFiltration hB τ] v) (hvU : ∀ ω, v ω ∈ cp.U)
    (hvb : ∃ M : ℝ, ∀ ω, ‖v ω‖ ≤ M)
    (y₁ : ℝ → ℝ≥0 → Ω → Fin n → ℝ)
    (hy₁ : ∀ ε ∈ Set.Ioc (0 : ℝ) ((cp.T : ℝ) - τ),
      SolvesFirstVariation cp (brownianFiltration hB) P B y u (spike u τ ε v) (y₁ ε)) :
    ∃ r : ℝ → ℝ, r =o[𝓝[>] (0 : ℝ)] (fun ε => ε) ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      r ε ≤
        (∫ ω, ∫ s in Set.Icc (0 : ℝ) cp.T,
            (ham cp (y s.toNNReal ω) (spike u τ ε v s.toNNReal ω) (p s.toNNReal ω)
                (fun j => K j s.toNNReal ω)
              - ham cp (y s.toNNReal ω) (u s.toNNReal ω) (p s.toNNReal ω)
                (fun j => K j s.toNNReal ω)) ∂volume ∂P)
        + (1 / 2 : ℝ) * (∫ ω, ∫ s in Set.Icc (0 : ℝ) cp.T,
            y₁ ε s.toNNReal ω ⬝ᵥ (hamXX cp (y s.toNNReal ω) (u s.toNNReal ω) (p s.toNNReal ω)
                (fun j => K j s.toNNReal ω) *ᵥ y₁ ε s.toNNReal ω) ∂volume ∂P)
        + (1 / 2 : ℝ) * ∫ ω, y₁ ε cp.T ω ⬝ᵥ (hess cp.h (y cp.T ω) *ᵥ y₁ ε cp.T ω) ∂P := by sorry

end Peng1990.SMP
