-- Prove2me | Theorems.Thm_RobustUncLP_Ellipsoidal_theorem_3_1
-- name    : RobustUncLP.Ellipsoidal.theorem_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T12:29:39.035037+00:00
-- url     : https://prove2.me/theorems/2737d1fc-b2e4-4ce6-b702-95245a0b4946
-- title:
--   Theorem 3.1, p. 9 — with ellipsoidal uncertainty, x is robust feasible iff fᵀx = 1 and x extends to a solution of the conic quadratic systems (𝒞_i)
-- statement:
--   Let the uncertainty set of the LP (6) be an **ellipsoidal uncertainty**
--   $$\mathcal U = \bigcap_{\ell=0}^k U(\Pi_\ell, Q_\ell),\qquad U(\Pi_\ell, Q_\ell) = \{\Pi_\ell(u) \mid \|Q_\ell u\| \le 1\},\quad \Pi_\ell(u) = P^0_\ell + \sum_j u_j P^j_\ell,$$
--   which is bounded (condition B) and satisfies the Slater condition C. Then for every $x \in \mathbb R^n$:
--   $$x \in G_{\mathcal U} \iff f^Tx = 1 \ \text{ and, for every } i = 1,\dots,m,\ \exists\, \lambda^{(i)}, \{\mu^{(i)}_\ell, \nu^{(i)}_\ell\}_{\ell=0}^k \text{ such that } (x, \lambda^{(i)}, \mu^{(i)}, \nu^{(i)}) \text{ satisfies } (\mathcal C_i).$$
--   Here $(\mathcal C_i)$ is the system of the `SystemC` definition. Its constraints are linear in $(x, \lambda, \mu, \nu)$ except for the second-order cone constraints $\|\mu_\ell^{(i)}\| \le \nu_\ell^{(i)}$, and its data are the coefficients $P^j_\ell$ and $Q_\ell$.
--
--   The page states Theorem 3.1 as: "The robust counterpart $(P_{\mathcal U})$ of an uncertain LP problem with general ellipsoidal uncertainty can be converted to a conic quadratic program." Its proof (Appendix, p. 16) concludes: "$x$ is robust feasible if and only if it can be extended to a feasible solution of (CQP)". (CQP) minimizes $c^Tx$ subject to $(\mathcal C_i)$ for $i = 1,\dots,m$ and $f^Tx = 1$. The robust feasible set is therefore the projection of the feasible set of an explicit conic quadratic program, so $(P_{\mathcal U})$ and (CQP) have the same optimal value and the same optimal $x$.
--
--   **Formalization Note** The formalized statement is the final sentence of the Appendix, which is the precise content of "can be converted". Conditions: B is `UncBounded`, a uniform bound on all matrix entries; C is required for all $\ell = 0,\dots,k$. The standing assumption of §2.1 that $\mathcal U$ is convex and closed is not added: an ellipsoidal uncertainty is automatically convex, and closedness is not used. The page writes $f^{(i)}[x]$ in $(\mathcal C_i)$ for $\varphi^{(i)}[x]$. Indices: rows $i$ are `Fin m`, $\ell = 0,\dots,k$ is `Fin (k + 1)`, and $\lambda^{(i)}$ consists of $k$ matrices indexed by `Fin k` (one per equation $\Pi_\ell(u^\ell) = \Pi_0(u^0)$, $\ell \ge 1$).
-- source:
--   Ben-Tal & Nemirovski, Robust solutions of uncertain linear programs, Oper. Res. Lett. 25 (1999); authors' manuscript, p. 9, Theorem 3.1, in the form proved in the Appendix, p. 16, claim (III) and (CQP) ("x is robust feasible if and only if it can be extended to a feasible solution of (CQP)")

import Mathlib
import Definitions.Def_RobustUncLP_Ellipsoidal_Setting
import Definitions.Def_RobustUncLP_Ellipsoidal_SystemC

namespace RobustUncLP.Ellipsoidal

open Matrix EllipsoidalData

/-- Theorem 3.1, p. 9, in the form proved in the Appendix, p. 16: for an ellipsoidal uncertainty
`𝒰` (conditions A, B, C), a point `x` is robust feasible iff `fᵀx = 1` and, for every row `i`,
`x` extends to a solution `(λ^{(i)}, μ^{(i)}, ν^{(i)})` of the conic quadratic system `(𝒞_i)`. -/
theorem theorem_3_1 {m n k : ℕ} (D : EllipsoidalData m n k) (f : Fin n → ℝ)
    (hB : UncBounded D.uncSet) (hC : D.SlaterC) :
    ∀ x : Fin n → ℝ, x ∈ RobustUncLP.WorstCase.robustFeas D.uncSet f ↔
      (f ⬝ᵥ x = 1 ∧ ∀ i : Fin m, ∃ (Λ : Fin k → Matrix (Fin m) (Fin n) ℝ)
        (μ : (ℓ : Fin (k + 1)) → Fin (D.M ℓ) → ℝ) (ν : Fin (k + 1) → ℝ), SystemC D x i Λ μ ν) := by sorry

end RobustUncLP.Ellipsoidal
