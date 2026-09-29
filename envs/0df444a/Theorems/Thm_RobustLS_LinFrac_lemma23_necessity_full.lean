-- Prove2me | Theorems.Thm_RobustLS_LinFrac_lemma23_necessity_full
-- name    : RobustLS.LinFrac.lemma23_necessity_full
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T13:39:25.875885+00:00
-- url     : https://prove2.me/theorems/e38b36d2-0da9-4e1b-8f3c-f7a17c908834
-- title:
--   Lemma 2.3, last sentence (strict form) — for 𝒟 = ℝ^{N×N} the scaled LMI is necessary, with S = sI, G = 0
-- statement:
--   Let $T_1 = T_1^T \in \mathbb R^{d\times d}$, $T_2 \in \mathbb R^{d\times N}$, $T_3 \in \mathbb R^{N\times d}$, $T_4 \in \mathbb R^{N\times N}$, and let $T(\Delta)$ be as in (9). Suppose that for every $\Delta \in \mathbb R^{N\times N}$ with $\|\Delta\| \le 1$ we have $\det(I - T_4\Delta) \neq 0$ and $T(\Delta) \succ 0$. Then there is $s > 0$ such that
--
--   $$
--   \begin{bmatrix} T_1 - sT_2T_2^T & T_3^T - sT_2T_4^T \\ T_3 - sT_4T_2^T & s(I - T_4T_4^T) \end{bmatrix} \succ 0 ,
--   $$
--
--   which is Lemma 2.3's condition with $S = sI$ and $G = 0$. For $\mathcal D = \mathbb R^{N\times N}$ the commutant scalings are exactly $\mathcal S = \{sI\}$ and $\mathcal G = \{0\}$, so this is the necessity of Lemma 2.3's condition for full perturbations.
--
--   It is the step that makes the SDP bound of Theorem 5.2 exact when the perturbation is unstructured.
--
--   **Formalization Note** The printed sentence ("If $\mathcal D = \mathbb R^{N\times N}$, the condition is necessary and sufficient") mixes a strict condition with the non-strict (9) and is false as printed: $T_1 = T_2 = T_3 = 0$ gives $T(\Delta) \equiv 0 \succeq 0$, but $T_1 - T_2ST_2^T = 0$ is not $\succ 0$. The strict form stated here (strict robust positivity implies the strict LMI) is the one Theorem 5.2 needs.
-- source:
--   El Ghaoui & Lebret, Robust Solutions to Least-Squares Problems with Uncertain Data, SIAM J. Matrix Anal. Appl. 18(4):1035–1064 (1997), p. 1039, §2.2, Lemma 2.3, last sentence (strict form)

import Mathlib
import Definitions.Def_RobustLS_LinFrac_Core

open Matrix

namespace RobustLS.LinFrac

/-- El Ghaoui & Lebret (1997), §2.2, Lemma 2.3, last sentence ("If 𝒟 = ℝ^{N×N}, the condition is
necessary and sufficient"), p. 1039 (PDF p. 5), **in its strict form**. As printed the necessity
is false, since the condition is strict (`≻ 0`) and (9) is not (`T₁ = T₂ = T₃ = 0` gives
`T(Δ) ≡ 0 ⪰ 0` but `T₁ − T₂ST₂ᵀ = 0` is not `≻ 0`). The strict form: if for every
`Δ ∈ ℝ^{N×N}` with `‖Δ‖ ≤ 1` we have `det(I − T₄Δ) ≠ 0` and `T(Δ) ≻ 0`, then the condition of
Lemma 2.3 holds with `S = sI` for some `s > 0` and `G = 0` (for `𝒟 = ℝ^{N×N}`, `𝒮` consists of
the multiples of `I` and `𝒢 = {0}`, so this is the lemma's "there exist `S ∈ 𝒮`, `G ∈ 𝒢`",
`S ≻ 0`). -/
theorem lemma23_necessity_full {d N : ℕ} (T₁ : Matrix (Fin d) (Fin d) ℝ) (hT₁ : T₁ = T₁ᵀ)
    (T₂ : Matrix (Fin d) (Fin N) ℝ) (T₃ : Matrix (Fin N) (Fin d) ℝ)
    (T₄ : Matrix (Fin N) (Fin N) ℝ)
    (h : ∀ Δ : Matrix (Fin N) (Fin N) ℝ, specNorm Δ ≤ 1 →
      (1 - T₄ * Δ).det ≠ 0 ∧ (lftT T₁ T₂ T₃ T₄ Δ).PosDef) :
    ∃ s : ℝ, 0 < s ∧ (lemma23Block T₁ T₂ T₃ T₄ (s • 1) 0).PosDef := by sorry

end RobustLS.LinFrac
