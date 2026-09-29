-- Prove2me | Theorems.Thm_Peng1990_SMP_second_order_adjoint_exists
-- name    : Peng1990.SMP.second_order_adjoint_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T23:34:48.623214+00:00
-- url     : https://prove2.me/theorems/79d8315e-1e1e-45f0-bba4-93a2eb932ef8
-- title:
--   Eq. (17) — existence and uniqueness of the second-order adjoint process $(P,Q)$
-- statement:
--   Assume (3), let $u$ be admissible with trajectory $y$, and let $(p,K)$ be a first-order adjoint process (13). Let $\mathbb R^{n,n}$ be the space of real symmetric $n\times n$ matrices with scalar product $(A_1,A_2)_*=\operatorname{tr}(A_1A_2)$, and for symmetric-valued $(\Phi,\Psi)\in L^2_{\mathcal F}(0,T;\mathbb R^{n,n})\times(L^2_{\mathcal F}(0,T;\mathbb R^{n,n}))^d$ let $Z$ solve
--   $$dZ=\Big[Zg_x^*+g_xZ+\sum_{j=1}^d\sigma^j_xZ\sigma^{j*}_x+\Phi\Big]dt+\sum_{j=1}^d\big[Z\sigma^{j*}_x+\sigma^j_xZ+\psi_j\big]dB^j,\qquad Z(0)=0 .$$
--   Set $M(\Phi,\Psi)=E\int_0^T(Z(t),H_{xx}(t))_*\,dt+E(Z(T),h_{xx}(y(T)))_*$ with $H_{xx}(t)=H_{xx}(y(t),u(t),p(t),K(t))$. Then there is $(P,Q)\in L^2_{\mathcal F}(0,T;\mathbb R^{n,n})\times(L^2_{\mathcal F}(0,T;\mathbb R^{n,n}))^d$ with
--   $$M(\Phi,\Psi)=E\int_0^T\Big[(P(t),\Phi(t))_*+\sum_{j=1}^d(Q_j(t),\psi_j(t))_*\Big]dt\tag{17}$$
--   for all such $(\Phi,\Psi)$, and any two such pairs agree $dt\otimes dP$-almost everywhere.
--
--   $(P,Q)$ is the second-order adjoint process: it represents the quadratic term of (14).
--
--   **Formalization Note** Symmetry of $P,Q$ and of the test processes is required at every $(t,\omega)$ with $t\le T$. The pair $(y,u)$ need only be admissible. The page writes both $Q_j$ and $Q^j$, $\psi_j$ and $\Psi^j$ for the same objects.
-- source:
--   Peng, A General Stochastic Maximum Principle for Optimal Control Problems, SIAM J. Control Optim. 28(4), 1990, https://doi.org/10.1137/0328054, p. 973, the symmetric matrix-valued system, (16), (17)

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_Peng1990_SMP_ControlProblem
import Definitions.Def_Peng1990_SMP_Adjoint

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics
open scoped ENNReal NNReal Matrix

namespace Peng1990.SMP

theorem second_order_adjoint_exists {Ω : Type*} [MeasurableSpace Ω] {n k d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (cp : ControlProblem n k d) (h3 : Assumption3 cp)
    (B : ℝ≥0 → Ω → Fin d → ℝ) (hB : IsStdBrownian P B)
    (y : ℝ≥0 → Ω → Fin n → ℝ) (u : ℝ≥0 → Ω → Fin k → ℝ)
    (hu : IsAdmissible cp (brownianFiltration hB) P u)
    (hy : SolvesState cp (brownianFiltration hB) P B u y)
    (p : ℝ≥0 → Ω → Fin n → ℝ) (K : Fin d → ℝ≥0 → Ω → Fin n → ℝ)
    (hpK : RepresentsI cp (brownianFiltration hB) P B y u p K) :
    (∃ (Pm : ℝ≥0 → Ω → Matrix (Fin n) (Fin n) ℝ)
        (Q : Fin d → ℝ≥0 → Ω → Matrix (Fin n) (Fin n) ℝ),
      RepresentsM cp (brownianFiltration hB) P B y u p K Pm Q) ∧
    ∀ (Pm Pm' : ℝ≥0 → Ω → Matrix (Fin n) (Fin n) ℝ)
      (Q Q' : Fin d → ℝ≥0 → Ω → Matrix (Fin n) (Fin n) ℝ),
      RepresentsM cp (brownianFiltration hB) P B y u p K Pm Q →
      RepresentsM cp (brownianFiltration hB) P B y u p K Pm' Q' →
      ∀ᵐ q ∂((volume.restrict (Set.Icc (0 : ℝ) cp.T)).prod P),
        Pm q.1.toNNReal q.2 = Pm' q.1.toNNReal q.2 ∧
        ∀ j, Q j q.1.toNNReal q.2 = Q' j q.1.toNNReal q.2 := by sorry

end Peng1990.SMP
