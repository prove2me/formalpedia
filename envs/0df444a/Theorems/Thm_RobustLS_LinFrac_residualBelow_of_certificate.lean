-- Prove2me | Theorems.Thm_RobustLS_LinFrac_residualBelow_of_certificate
-- name    : RobustLS.LinFrac.residualBelow_of_certificate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T13:40:29.152085+00:00
-- url     : https://prove2.me/theorems/2fde47c1-b984-4794-9743-986577f322f7
-- title:
--   §5.4, Eqs. (38)–(39) (corrected: S ≻ 0, GΔ skew) — a feasible (λ, S, G) certifies λ > r_𝒟(A, b, x)
-- statement:
--   In the linear-fractional model of §5.2 with $\rho = 1$, fix $x \in \mathbb R^m$ and $\lambda \in \mathbb R$. Let $S \in \mathcal S$ and $G \in \mathcal G$ (the symmetric and skew-symmetric matrices commuting with every element of $\mathcal D$), with $S \succ 0$ and $G\Delta$ skew-symmetric for every $\Delta \in \mathcal D$. If
--
--   $$
--   \mathcal F(\lambda, S, G, x) = \begin{bmatrix} \Theta & \begin{matrix} Ax - b \\ R_Ax - R_b \end{matrix} \\ \begin{matrix} (Ax-b)^T & (R_Ax - R_b)^T \end{matrix} & \lambda \end{bmatrix} \succ 0, \qquad \Theta = \begin{bmatrix} \lambda I - LSL^T & -LSD^T + LG \\ -DSL^T + G^TL^T & S + DG - GD^T - DSD^T \end{bmatrix},
--   $$
--
--   then $\lambda > r_{\mathcal D}(A,b,x)$; in particular $\det(I - D\Delta) \neq 0$ for every $\Delta \in \mathcal D$ with $\|\Delta\| \le 1$.
--
--   The condition is a linear matrix inequality in $(\lambda, S, G)$, so minimizing $\lambda$ over it is a semidefinite program whose value bounds the (NP-hard) worst-case residual from above.
--
--   **Formalization Note** Two hypotheses are added to the printed sentence, both required by Lemma 2.3 as it is proved. $S \succ 0$ is dropped on p. 1048; without it, $N = n = m = 1$, $D = 2$, $L = 1$, $A = b = R_A = R_b = 0$, $x = 0$, $S = -1$, $G = 0$ satisfy (38) for every $\lambda > 1/3$, while $\Delta = 1/2$ makes $I - D\Delta$ singular, so $r_{\mathcal D} = \infty$. "$G\Delta$ skew-symmetric for $\Delta \in \mathcal D$" (automatic for symmetric structures such as (36), and for $G = 0$) is the identity $p^TGq = 0$ used in Lemma 2.3's proof; without it, $n = m = 1$, $N = 2$, $\mathcal D = \operatorname{span}\{I, J\}$ with $J = \begin{bmatrix}0&1\\-1&0\end{bmatrix}$, $A = 0$, $b = -1$, $x = 0$, $L = [1\ 0]$, $R_A = 0$, $R_b = (0,-1)^T$, $D = 0$, $S = I/\sqrt2$, $G = J/\sqrt2$ and $\lambda = 3/2$ satisfy (38), while $\Delta = J$ gives residual $2$.
-- source:
--   El Ghaoui & Lebret, Robust Solutions to Least-Squares Problems with Uncertain Data, SIAM J. Matrix Anal. Appl. 18(4):1035–1064 (1997), p. 1048, §5.4, Eqs. (38)–(39) (corrected)

import Mathlib
import Definitions.Def_RobustLS_LinFrac_Core

open Matrix

namespace RobustLS.LinFrac

/-- El Ghaoui & Lebret (1997), §5.4, p. 1048 (PDF p. 14), Eqs. (38)–(39), **corrected**: "Using
Lemma 2.3, we obtain that λ > r_𝒟(A, b, x) holds if there exist S ∈ 𝒮, G ∈ 𝒢, such that
𝓕(λ, S, G, x) > 0." Two hypotheses are added, both required by Lemma 2.3 as it is actually
proved: `S ≻ 0` (dropped from (38) on the page; without it, `N = n = m = 1`, `D = 2`, `L = 1`,
`A = b = R_A = R_b = 0`, `x = 0`, `S = −1`, `G = 0` satisfies (38) for every `λ > 1/3` while
`Δ = 1/2` makes `I − DΔ` singular, so `r_𝒟 = ∞`), and `GΔ` skew-symmetric for every `Δ ∈ 𝒟`
(without it, `n = m = 1`, `N = 2`, `𝒟 = span{I, J}`, `J = [[0,1],[−1,0]]`, `A = 0`, `b = −1`,
`x = 0`, `L = [1 0]`, `R_A = 0`, `R_b = (0, −1)`, `D = 0`, `S = I/√2`, `G = J/√2`,
`λ = 3/2` satisfies (38) while `Δ = J` gives residual `2`). -/
theorem residualBelow_of_certificate {n m N : ℕ} (𝒟 : Submodule ℝ (Matrix (Fin N) (Fin N) ℝ))
    (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin n → ℝ) (L : Matrix (Fin n) (Fin N) ℝ)
    (RA : Matrix (Fin N) (Fin m) ℝ) (Rb : Fin N → ℝ) (D : Matrix (Fin N) (Fin N) ℝ)
    (x : Fin m → ℝ) (lam : ℝ) (S G : Matrix (Fin N) (Fin N) ℝ)
    (hS : S ∈ symCommutant 𝒟) (hG : G ∈ skewCommutant 𝒟)
    (hGΔ : ∀ Δ ∈ 𝒟, (G * Δ)ᵀ = -(G * Δ)) (hSpos : S.PosDef)
    (hF : (lmiF A b L RA Rb D x lam S G).PosDef) :
    ResidualBelow 𝒟 A b L RA Rb D x lam := by sorry

end RobustLS.LinFrac
