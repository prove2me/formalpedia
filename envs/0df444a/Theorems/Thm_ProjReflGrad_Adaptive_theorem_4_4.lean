-- Prove2me | Theorems.Thm_ProjReflGrad_Adaptive_theorem_4_4
-- name    : ProjReflGrad.Adaptive.theorem_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:15:56.536207+00:00
-- url     : https://prove2.me/theorems/e3f4051b-0d4d-4e9b-a29d-d7a76ddc7b71
-- title:
--   Theorem 4.4, p. 12 — the adaptive projected reflected gradient method converges weakly to a solution without knowing L
-- statement:
--   Let $H$ be a real Hilbert space, $C \subseteq H$ nonempty, closed and convex, and $F : H \to H$. Assume
--
--   1. **(C1)** the solution set $S$ of the variational inequality (1.1), find $x^* \in C$ with $\langle F(x^*), x - x^*\rangle \ge 0$ for all $x \in C$, is nonempty;
--   2. **(C2)** $F$ is monotone on $H$;
--   3. **(C3)** $F$ is $L$-Lipschitz on $H$ for some $L > 0$.
--
--   Let $\alpha \in (0, \sqrt2 - 1)$, $\lambda_{-1} > 0$ and $\bar\lambda > 0$, and let $(x_n), (y_n), (\lambda_n), (\tau_n)$ be any run of Algorithm 4.2. Then there is $x^* \in S$ with
--   $$x_n \rightharpoonup x^* \qquad\text{and}\qquad y_n \rightharpoonup x^*.$$
--
--   Algorithm 4.2 chooses its steps by the local rule (4.1) and a test, with at most two projections per iteration, and never uses $L$; the theorem shows that this adaptivity costs nothing in the convergence guarantee of the constant-step method.
--
--   **Formalization Note** Weak convergence is $\langle x_n, v\rangle \to \langle x^*, v\rangle$ for every $v \in H$. The run is any admissible run: the corrections $\lambda'_n$, $\tau'_n$ of step 4 range over all allowed values, and $\bar\lambda > 0$ is the only assumption on the cap. No lower bound on $(\lambda_n)$ is assumed.
-- source:
--   Malitsky, Projected Reflected Gradient Methods for Monotone Variational Inequalities, arXiv:1502.04968v1, p. 12, Theorem 4.4

import Mathlib
import Definitions.Def_ProjReflGrad_Adaptive_Setting

namespace ProjReflGrad.Adaptive

/-- Theorem 4.4 (Malitsky 2015, p. 12): assume (C1)–(C3). Then the sequences `(x_n)` and `(y_n)` of
any run of Algorithm 4.2 converge weakly to one and the same solution of the variational
inequality (1.1). The algorithm never uses the Lipschitz constant `L`. -/
theorem theorem_4_4 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : Set H) (hCcl : IsClosed C) (hCcv : Convex ℝ C) (F : H → H) (L : ℝ)
    (hC1 : (ProjReflGrad.Weak.solSet C F).Nonempty) (hC2 : ProjReflGrad.Weak.IsMonotoneMap F) (hL : 0 < L) (hC3 : ProjReflGrad.Weak.IsLipschitzMap F L)
    (α lamInit lamBar : ℝ) (hα0 : 0 < α) (hα1 : α < Real.sqrt 2 - 1) (hlamInit : 0 < lamInit)
    (hlamBar : 0 < lamBar) (x y : ℕ → H) (lam tau : ℕ → ℝ)
    (hrun : IsAdaptiveRun C F α lamInit lamBar x y lam tau) :
    ∃ xs ∈ ProjReflGrad.Weak.solSet C F, ProjReflGrad.Weak.IsWeakLimit x xs ∧ ProjReflGrad.Weak.IsWeakLimit y xs := by sorry

end ProjReflGrad.Adaptive
