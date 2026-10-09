-- Prove2me | Theorems.Thm_SLQSolv_MinSeq_corollary_4_7
-- name    : SLQSolv.MinSeq.corollary_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:21:26.910982+00:00
-- url     : https://prove2.me/theorems/3019123f-b84a-4e93-bc13-33a033b70bc6
-- title:
--   Corollary 4.7, p. 2291 — under (4.2), (SLQ) is uniquely open-loop solvable with the state-feedback optimal control (4.28)
-- statement:
--   Assume (H1)–(H2) and the uniform convexity condition (4.2): for some $\lambda>0$,
--
--   $$
--   J^0(0,0;u)\ge\lambda\,\mathbb E\int_0^T|u(s)|^2ds\qquad\forall u\in\mathcal U[0,T].
--   $$
--
--   Then for every $(t,x)\in[0,T)\times\mathbb R^n$:
--
--   1. Problem (SLQ) is uniquely open-loop solvable at $(t,x)$;
--   2. the Riccati equation (4.6) has a strongly regular solution $P$;
--   3. for every strongly regular solution $P$, the BSDE (4.11) has an adapted solution $(\eta,\zeta)$;
--   4. for every such $P$ and $(\eta,\zeta)$, with $\Theta=-(R+D^\top PD)^{-1}(B^\top P+D^\top PC+S)$ and $v=-(R+D^\top PD)^{-1}(B^\top\eta+D^\top\zeta+D^\top P\sigma+\rho)$, the closed-loop system
--
--   $$
--   dX^*=\big[(A+B\Theta)X^*+Bv+b\big]ds+\big[(C+D\Theta)X^*+Dv+\sigma\big]dW,\quad s\in[t,T],\qquad X^*(t)=x,
--   $$
--
--   has a solution, and for every solution $X^*$ the control $u^*=\Theta X^*+v$ of (4.28) is open-loop optimal at $(t,x)$.
--
--   Applied to the data with $R$ replaced by $R+\varepsilon I$, this is what makes each $u_\varepsilon$ of (6.2) the optimal control of the regularized problem in Section 6.
--
--   **Formalization Note** The page asserts the objects through the definite article ("the unique strongly regular solution", "the adapted solution", "the solution"); the statement makes their existence explicit and asserts optimality for every such solution. (H1)–(H2) are the standing assumptions; the state, cost, value function and optimality notions are those of the shared `Setting` module.
-- source:
--   Sun–Li–Yong, SIAM J. Control Optim. 54 (2016), Corollary 4.7, (4.28), p. 2291; (4.11), pp. 2285–2286

import Mathlib
import Definitions.Def_SLQSolv_MinSeq_Sequence

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal Matrix

namespace SLQSolv.MinSeq

/-- Corollary 4.7, p. 2291: under (H1)–(H2) and the uniform convexity (4.2), Problem (SLQ) is
uniquely open-loop solvable at every `(t, x) ∈ [0, T) × ℝⁿ`; the Riccati equation (4.6) has a
strongly regular solution `P`; for it the BSDE (4.11) has an adapted solution `(η, ζ)`; the
closed-loop system with `Θ = −(R + DᵀPD)⁻¹(BᵀP + DᵀPC + S)` and
`v = −(R + DᵀPD)⁻¹(Bᵀη + Dᵀζ + DᵀPσ + ρ)` has a solution `X*` from `(t, x)`; and
`u* = ΘX* + v` of (4.28) is an open-loop optimal control at `(t, x)`. -/
theorem corollary_4_7 {Ω : Type*} [MeasurableSpace Ω] {n m : ℕ} (Bs : Basis Ω) (d : Data Ω n m)
    (h1 : H1 Bs d) (h2 : H2 Bs d)
    (hunif : IsUnifConvex Bs d 0) (t : ℝ≥0) (ht : t < d.T) (x : Fin n → ℝ) :
    UniquelyOpenLoopSolvableAt Bs d t x ∧ (∃ P, IsStronglyRegular d P) ∧
      ∀ P, IsStronglyRegular d P →
        (∃ η ζ, IsAdjointEta Bs d P η ζ) ∧
        ∀ η ζ, IsAdjointEta Bs d P η ζ →
          (∃ X, IsClosedLoopState Bs d t (thetaOf d P) (vOf d P η ζ) x X) ∧
          ∀ X, IsClosedLoopState Bs d t (thetaOf d P) (vOf d P η ζ) x X →
            IsOpenLoopOptimal Bs d t x (fun s ω => thetaOf d P s *ᵥ X s ω + vOf d P η ζ s ω) := by sorry

end SLQSolv.MinSeq
