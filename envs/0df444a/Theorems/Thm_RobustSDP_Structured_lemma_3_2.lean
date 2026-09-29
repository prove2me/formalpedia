-- Prove2me | Theorems.Thm_RobustSDP_Structured_lemma_3_2
-- name    : RobustSDP.Structured.lemma_3_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:01:33.743141+00:00
-- url     : https://prove2.me/theorems/15442725-841c-48e8-a013-6f2d9e770061
-- title:
--   Lemma 3.2 — scaled sufficient condition for a robust LMI under a structured LFR perturbation (corrected (13))
-- statement:
--   Let $F = F^T \in \mathbb{R}^{n\times n}$, $L \in \mathbb{R}^{n\times p}$, $R \in \mathbb{R}^{q\times n}$ and $D \in \mathbb{R}^{q\times p}$ be real matrices, let $\mathcal{D}$ be a linear subspace of $\mathbb{R}^{p\times q}$, and let $\mathcal{B}$ be its scaling set: the triples $(S,T,G) \in \mathbb{R}^{p\times p}\times\mathbb{R}^{q\times q}\times\mathbb{R}^{p\times q}$ with $S\Delta = \Delta T$ and $G\Delta^T = -\Delta G^T$ for every $\Delta \in \mathcal{D}$.
--
--   Suppose there is a triple $(S,T,G) \in \mathcal{B}$ with $S \succ 0$, $T \succ 0$ and
--   $$\begin{bmatrix} F - LSL^T & R^T - LSD^T + LG \\ R - DSL^T + G^T L^T & T - DSD^T + DG + G^T D^T\end{bmatrix} \succ 0. \qquad (13)$$
--   Then for every $\Delta \in \mathcal{D}$ with $\|\Delta\| \le 1$ we have $\det(I - D\Delta) \neq 0$ and
--   $$F + L\Delta(I - D\Delta)^{-1}R + R^T(I - D\Delta)^{-T}\Delta^T L^T \succ 0. \qquad (12)$$
--
--   Here $\|\Delta\|$ is the largest singular value and $X \succ 0$ means that $X$ is symmetric positive definite. The lemma generalizes the sufficiency half of the full-perturbation Lemma 3.1 to an arbitrary subspace of perturbations: the scaling matrices $S$, $T$, $G$ exploit the structure of $\mathcal{D}$ to reduce the conservatism of a single multiplier. It is the tool behind Theorem 3.2 and Theorem 5.6.
--
--   **Correction.** (13) as printed is dimensionally inconsistent (it contains $LG$, $DSL$ and $DG$ with $G \in \mathbb{R}^{q\times p}$ and bottom-left block $R - DSL - GL^T$, bottom-right $T - GD^T + DG - DSD^T$); we state the condition the proof yields, which coincides with the printed one when $G$ is square and skew-symmetric and $\mathcal{D}$ consists of symmetric matrices.
--
--   **Formalization Note** $\succ 0$ is `Matrix.PosDef`, which includes symmetry; the corrected block matrix is symmetric whenever $F$, $S$, $T$ are. $(I - D\Delta)^{-T}$ is written as the transpose of Mathlib's inverse; the determinant condition is part of the conclusion, so the inverse is never used at a singular matrix in the intended reading. The norm is the $\ell^2$ operator norm.
-- source:
--   El Ghaoui, Oustry and Lebret, Robust Solutions to Uncertain Semidefinite Programs, SIAM J. Optim. 9(1) (1998), p. 37, Lemma 3.2 with Eq. (11), (12), (13) (corrected)

import Mathlib
import Definitions.Def_RobustSDP_Structured_Model

open Matrix
open scoped Matrix.Norms.L2Operator

namespace RobustSDP.Structured

/-- Lemma 3.2, p. 37, with the matrix (13) and the `G`-part of (11) **corrected** (as printed,
(13) contains the undefined products `LG`, `DSL`, `DG`). Let `F = Fᵀ` (`n × n`), `L` (`n × p`),
`R` (`q × n`), `D` (`q × p`), and let `𝒟` be a linear subspace of `ℝ^{p×q}`. If some triple
`(S, T, G) ∈ 𝓑` (`scalingSet 𝒟`) has `S ≻ 0`, `T ≻ 0` and
`[[F − LSLᵀ, Rᵀ − LSDᵀ + LG], [R − DSLᵀ + GᵀLᵀ, T − DSDᵀ + DG + GᵀDᵀ]] ≻ 0`,
then for every `Δ ∈ 𝒟` with `‖Δ‖ ≤ 1` (spectral norm): `det (I − DΔ) ≠ 0` and
`F + LΔ(I − DΔ)⁻¹R + Rᵀ(I − DΔ)⁻ᵀΔᵀLᵀ ≻ 0` (12). -/
theorem lemma_3_2 {n p q : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) (hF : F.IsSymm)
    (L : Matrix (Fin n) (Fin p) ℝ) (R : Matrix (Fin q) (Fin n) ℝ) (D : Matrix (Fin q) (Fin p) ℝ)
    (𝒟 : Submodule ℝ (Matrix (Fin p) (Fin q) ℝ))
    (S : Matrix (Fin p) (Fin p) ℝ) (T : Matrix (Fin q) (Fin q) ℝ) (G : Matrix (Fin p) (Fin q) ℝ)
    (hB : (S, T, G) ∈ scalingSet 𝒟) (hS : S.PosDef) (hT : T.PosDef)
    (hLMI : (fromBlocks (F - L * S * Lᵀ) (Rᵀ - L * S * Dᵀ + L * G) (R - D * S * Lᵀ + Gᵀ * Lᵀ)
      (T - D * S * Dᵀ + D * G + Gᵀ * Dᵀ)).PosDef) :
    ∀ Δ ∈ 𝒟, ‖Δ‖ ≤ 1 →
      (1 - D * Δ).det ≠ 0 ∧
        (F + L * Δ * (1 - D * Δ)⁻¹ * R + Rᵀ * ((1 - D * Δ)⁻¹)ᵀ * Δᵀ * Lᵀ).PosDef := by sorry

end RobustSDP.Structured
