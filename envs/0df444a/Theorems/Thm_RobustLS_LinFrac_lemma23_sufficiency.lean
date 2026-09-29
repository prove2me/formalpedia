-- Prove2me | Theorems.Thm_RobustLS_LinFrac_lemma23_sufficiency
-- name    : RobustLS.LinFrac.lemma23_sufficiency
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T13:38:53.528479+00:00
-- url     : https://prove2.me/theorems/964b4c72-208e-46d6-b7a7-728a0184b743
-- title:
--   Lemma 2.3 (sufficiency, corrected) — structured S-procedure with scalings S ∈ 𝒮, G ∈ 𝒢
-- statement:
--   Let $\mathcal D$ be a linear subspace of $\mathbb R^{N\times N}$, and let $\mathcal S$ (resp. $\mathcal G$) be the set of symmetric (resp. skew-symmetric) matrices that commute with every element of $\mathcal D$. Let $T_1 = T_1^T \in \mathbb R^{d\times d}$, $T_2 \in \mathbb R^{d\times N}$, $T_3 \in \mathbb R^{N\times d}$, $T_4 \in \mathbb R^{N\times N}$ and let $T(\Delta)$ be as in (9). Suppose there exist $S \in \mathcal S$ and $G \in \mathcal G$ with $S \succ 0$, with $G\Delta$ skew-symmetric for every $\Delta \in \mathcal D$, and with
--
--   $$
--   \begin{bmatrix} T_1 - T_2ST_2^T & T_3^T - T_2ST_4^T + T_2G \\ T_3 - T_4ST_2^T - GT_2^T & S - GT_4^T + T_4G - T_4ST_4^T \end{bmatrix} \succ 0 .
--   $$
--
--   Then for every $\Delta \in \mathcal D$ with $\|\Delta\| \le 1$, $\det(I - T_4\Delta) \neq 0$ and $T(\Delta) \succ 0$.
--
--   This is the structured version of Lemma 2.2: the scalings $S$, $G$ exploit the structure of $\mathcal D$ and give a sufficient LMI condition for robust positivity over a structured ball.
--
--   **Formalization Note** Two changes to the printed lemma. (i) The hypothesis "$G\Delta$ skew-symmetric for every $\Delta \in \mathcal D$" is added. It is exactly the identity $p^TGq = 0$ (with $p = \Delta^Tq$) that the paper's proof uses, and it holds automatically when every element of $\mathcal D$ is symmetric (e.g. the diagonal structures (36)) or when $G = 0$ (e.g. $\mathcal D = \mathbb R^{N\times N}$). Without it the lemma is false: take $N = 2$, $d = 1$, $\mathcal D = \operatorname{span}\{I, J\}$ with $J = \begin{bmatrix} 0 & 1 \\ -1 & 0\end{bmatrix}$ (so $\mathcal S = \{sI\}$, $\mathcal G = \{gJ\}$), $T_1 = 1$, $T_2 = [1\ 0]$, $T_4 = 0$, $G = J$, $T_3 = GT_2^T$, $S = sI$ with $0 < s < 1$; the block matrix is $\operatorname{diag}(1 - s, sI) \succ 0$, but $\Delta = J \in \mathcal D$ has $\|J\| = 1$ and $T(J) = -1$. (ii) The conclusion is the strict $T(\Delta) \succ 0$, which the same hypotheses give and which §5.4 uses; the printed (9) asks only $T(\Delta) \succeq 0$, which follows.
-- source:
--   El Ghaoui & Lebret, Robust Solutions to Least-Squares Problems with Uncertain Data, SIAM J. Matrix Anal. Appl. 18(4):1035–1064 (1997), p. 1039, §2.2, Lemma 2.3 (sufficiency, corrected)

import Mathlib
import Definitions.Def_RobustLS_LinFrac_Core

open Matrix

namespace RobustLS.LinFrac

/-- El Ghaoui & Lebret (1997), §2.2, Lemma 2.3, sufficiency, p. 1039 (PDF p. 5), **corrected**.
Let `𝒟` be a subspace of `ℝ^{N×N}`, `𝒮` (resp. `𝒢`) the symmetric (resp. skew-symmetric)
matrices commuting with every element of `𝒟`, `T₁ = T₁ᵀ ∈ ℝ^{d×d}`, `T₂ ∈ ℝ^{d×N}`,
`T₃ ∈ ℝ^{N×d}`, `T₄ ∈ ℝ^{N×N}`. If `S ∈ 𝒮`, `G ∈ 𝒢`, `S ≻ 0` and the block matrix of the lemma
is positive definite, then for every `Δ ∈ 𝒟` with `‖Δ‖ ≤ 1`: `det(I − T₄Δ) ≠ 0` and
`T(Δ) ≻ 0`.
Corrections to the printed lemma: (i) the extra hypothesis that `GΔ` is skew-symmetric for every
`Δ ∈ 𝒟` — this is exactly the identity `pᵀGq = 0` (`p = Δᵀq`) the proof uses; without it the
lemma is false (`N = 2`, `d = 1`, `𝒟 = span{I, J}` with `J = [[0,1],[−1,0]]`, `T₁ = 1`,
`T₂ = [1 0]`, `T₃ = GT₂ᵀ`, `T₄ = 0`, `S = sI` with `0 < s < 1`, `G = J`: the condition holds
but `T(J) = −1`); it holds automatically when every element of `𝒟` is symmetric or when
`G = 0`. (ii) The conclusion is the strict `T(Δ) ≻ 0`, which the same hypotheses give and which
§5.4 uses; the printed conclusion (9) is `T(Δ) ⪰ 0`, implied by it. -/
theorem lemma23_sufficiency {d N : ℕ} (𝒟 : Submodule ℝ (Matrix (Fin N) (Fin N) ℝ))
    (T₁ : Matrix (Fin d) (Fin d) ℝ) (hT₁ : T₁ = T₁ᵀ)
    (T₂ : Matrix (Fin d) (Fin N) ℝ) (T₃ : Matrix (Fin N) (Fin d) ℝ)
    (T₄ S G : Matrix (Fin N) (Fin N) ℝ) (hS : S ∈ symCommutant 𝒟) (hG : G ∈ skewCommutant 𝒟)
    (hGΔ : ∀ Δ ∈ 𝒟, (G * Δ)ᵀ = -(G * Δ)) (hSpos : S.PosDef)
    (hblock : (lemma23Block T₁ T₂ T₃ T₄ S G).PosDef) :
    ∀ Δ ∈ 𝒟, specNorm Δ ≤ 1 →
      (1 - T₄ * Δ).det ≠ 0 ∧ (lftT T₁ T₂ T₃ T₄ Δ).PosDef := by sorry

end RobustLS.LinFrac
