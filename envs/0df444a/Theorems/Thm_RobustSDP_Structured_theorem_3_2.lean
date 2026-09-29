-- Prove2me | Theorems.Thm_RobustSDP_Structured_theorem_3_2
-- name    : RobustSDP.Structured.theorem_3_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:02:32.107628+00:00
-- url     : https://prove2.me/theorems/f38486a4-fbc6-40b1-bb68-a570268616c2
-- title:
--   Theorem 3.2 — the scaled SDP is an inner approximation of the structured robust feasible set (corrected LMI)
-- statement:
--   Let $F(x) = F_0 + \sum_{i=1}^m x_i F_i$ with symmetric $F_i \in \mathbb{R}^{n\times n}$ and $R(x) = R_0 + \sum_{i=1}^m x_i R_i$ with $R_i \in \mathbb{R}^{q\times n}$ be affine, let $L \in \mathbb{R}^{n\times p}$, $D \in \mathbb{R}^{q\times p}$, let $\mathcal{D}$ be a linear subspace of $\mathbb{R}^{p\times q}$ with scaling set $\mathcal{B}$ (triples $(S,T,G)$ with $S\Delta = \Delta T$, $G\Delta^T = -\Delta G^T$ for all $\Delta \in \mathcal{D}$), and let $\rho > 0$. Write $\mathcal{X}_\rho$ for the robust feasible set (2) and $\mathbf{F}(x,\Delta)$ for the linear-fractional representation (5).
--
--   If $x \in \mathbb{R}^m$ admits $(S,T,G) \in \mathcal{B}$ with $S \succ 0$, $T \succ 0$ and
--   $$\begin{bmatrix} F(x) - LSL^T & R(x)^T - LSD^T + LG \\ R(x) - DSL^T + G^T L^T & \rho^{-2}T - DSD^T + DG + G^T D^T\end{bmatrix} \succ 0,$$
--   then $x \in \mathcal{X}_\rho$; moreover $\mathbf{F}(x,\Delta) \succ 0$ for every $\Delta \in \mathcal{D}$ with $\|\Delta\| \le \rho$.
--
--   The paper states the theorem as "an upper bound on the RSDP (4) and a corresponding solution $x$ can be computed by solving the SDP in variables $x, S, T, G$: $\inf c^Tx$ subject to the constraints above". Its mathematical content is the inclusion stated here: the projection onto $x$ of the SDP's feasible set lies inside the robust feasible set, so every SDP-feasible $x$ is robustly feasible and the SDP value bounds the RSDP value from above (the value form is a separate item). The general robust SDP with structured perturbations is NP-hard, and this inclusion is what makes a tractable conservative approximation available.
--
--   **Correction.** The LMI of Theorem 3.2 repeats the misprint of (13): as printed it is dimensionally inconsistent; we state the condition the proof yields, which coincides with the printed one when $G$ is square and skew-symmetric and $\mathcal{D}$ consists of symmetric matrices.
--
--   **Formalization Note** "Can be computed by solving the SDP" is read as the inclusion above, for every $x$, with the SDP variables $(S,T,G)$ existentially quantified. The conclusion is stated in its strict form ($\mathbf{F}(x,\Delta) \succ 0$), which the proof gives, together with membership in $\mathcal{X}_\rho$ (non-strict, with $\det(I - D\Delta) \neq 0$). The standing assumption $\rho > 0$ of §3 is a hypothesis; the symmetry of $F_0,\dots,F_m$ (notation of (1)) is a hypothesis. The norm is the largest singular value; $\succ 0$ is `Matrix.PosDef`.
-- source:
--   El Ghaoui, Oustry and Lebret, Robust Solutions to Uncertain Semidefinite Programs, SIAM J. Optim. 9(1) (1998), p. 37, Theorem 3.2 (LMI corrected as in Lemma 3.2); p. 35, Eq. (2), (4), (5); p. 36, "we fix ρ > 0"

import Mathlib
import Definitions.Def_RobustSDP_Structured_Model

open Matrix
open scoped Matrix.Norms.L2Operator

namespace RobustSDP.Structured

/-- Theorem 3.2, p. 37, read as an inner approximation of the robust feasible set, with the LMI
**corrected** as in Lemma 3.2. Let `F(x) = F₀ + ∑ xᵢFᵢ` (`Fᵢ` symmetric) and
`R(x) = R₀ + ∑ xᵢRᵢ` be affine, `L`, `D` fixed, `𝒟` a linear subspace of `ℝ^{p×q}` and `ρ > 0`.
If `x` admits `(S, T, G) ∈ 𝓑` with `S ≻ 0`, `T ≻ 0` and
`[[F(x) − LSLᵀ, R(x)ᵀ − LSDᵀ + LG], [R(x) − DSLᵀ + GᵀLᵀ, ρ⁻²T − DSDᵀ + DG + GᵀDᵀ]] ≻ 0`,
then `x` lies in the robust feasible set `𝒳_ρ` (2), and in fact `F(x, Δ) ≻ 0` for every
`Δ ∈ 𝒟` with `‖Δ‖ ≤ ρ`. -/
theorem theorem_3_2 {m n p q : ℕ} (Fs : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ)
    (hFs : ∀ i, (Fs i).IsSymm) (Rs : Fin (m + 1) → Matrix (Fin q) (Fin n) ℝ)
    (L : Matrix (Fin n) (Fin p) ℝ) (D : Matrix (Fin q) (Fin p) ℝ)
    (𝒟 : Submodule ℝ (Matrix (Fin p) (Fin q) ℝ)) (ρ : ℝ) (hρ : 0 < ρ) (x : Fin m → ℝ)
    (hx : ∃ (S : Matrix (Fin p) (Fin p) ℝ) (T : Matrix (Fin q) (Fin q) ℝ)
        (G : Matrix (Fin p) (Fin q) ℝ), (S, T, G) ∈ scalingSet 𝒟 ∧ S.PosDef ∧ T.PosDef ∧
          (structuredLMI (affineMap Fs x) (affineMap Rs x) L D S T G ρ).PosDef) :
    x ∈ robustFeasibleSet Fs Rs L D 𝒟 ρ ∧
      ∀ Δ ∈ 𝒟, ‖Δ‖ ≤ ρ → (lfr (affineMap Fs x) (affineMap Rs x) L D Δ).PosDef := by sorry

end RobustSDP.Structured
