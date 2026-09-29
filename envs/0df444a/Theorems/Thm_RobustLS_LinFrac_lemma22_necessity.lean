-- Prove2me | Theorems.Thm_RobustLS_LinFrac_lemma22_necessity
-- name    : RobustLS.LinFrac.lemma22_necessity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:38:23.899269+00:00
-- url     : https://prove2.me/theorems/cf6201c4-3a83-437e-8bb9-ffde478a73aa
-- title:
--   Lemma 2.2 (only if, corrected: T₂ ≠ 0 or T₃ = 0) — robust T(Δ) ⪰ 0 on the unit ball implies ‖T₄‖ < 1 and (10) for some τ ≥ 0
-- statement:
--   Let $T_1 = T_1^T \in \mathbb R^{d\times d}$, $T_2 \in \mathbb R^{d\times k}$, $T_3 \in \mathbb R^{l\times d}$, $T_4 \in \mathbb R^{l\times k}$, and let $T(\Delta)$ be as in (9). Assume $T_2 \neq 0$ or $T_3 = 0$. If for every $\Delta \in \mathbb R^{k\times l}$ with $\|\Delta\| \le 1$ we have $\det(I - T_4\Delta) \neq 0$ and $T(\Delta) \succeq 0$, then $\|T_4\| < 1$ and there exists $\tau \ge 0$ with
--
--   $$
--   \begin{bmatrix} T_1 - \tau T_2T_2^T & T_3^T - \tau T_2T_4^T \\ T_3 - \tau T_4T_2^T & \tau(I - T_4T_4^T) \end{bmatrix} \succeq 0 . \qquad (10)
--   $$
--
--   Together with the "if" half, this makes the scalar LMI (10) an exact test for robust positivity of $T(\Delta)$ over the full unit ball.
--
--   **Formalization Note** The printed lemma has no hypothesis on $T_2, T_3$, and its "only if" is then false: for $d = k = l = 1$, $T_1 = T_2 = T_4 = 0$, $T_3 = 1$, we have $T(\Delta) \equiv 0 \succeq 0$ and $\det(I - T_4\Delta) = 1$, yet $\begin{bmatrix} 0 & 1 \\ 1 & \tau\end{bmatrix}$ is never positive semidefinite. The paper's proof calls the cases $T_2 = 0$ or $T_3 = 0$ "obvious"; exactly the case $T_2 = 0 \neq T_3$ fails, and it is excluded here.
-- source:
--   El Ghaoui & Lebret, Robust Solutions to Least-Squares Problems with Uncertain Data, SIAM J. Matrix Anal. Appl. 18(4):1035–1064 (1997), p. 1038, §2.2, Lemma 2.2 ("only if" direction, corrected), Eqs. (9)–(10); proof p. 1039

import Mathlib
import Definitions.Def_RobustLS_LinFrac_Core

open Matrix

namespace RobustLS.LinFrac

/-- El Ghaoui & Lebret (1997), §2.2, Lemma 2.2, "only if" direction, p. 1038 (PDF p. 4),
**corrected**: stated under `T₂ ≠ 0 ∨ T₃ = 0`. As printed (without that hypothesis) the
direction is false: `d = k = l = 1`, `T₁ = T₂ = T₄ = 0`, `T₃ = 1` gives `T(Δ) ≡ 0 ⪰ 0` and
`det(I − T₄Δ) = 1`, but `[[0, 1], [1, τ]]` is never positive semidefinite. (The proof, p. 1039,
treats `T₂ = 0` or `T₃ = 0` as "obvious"; only `T₂ = 0 ≠ T₃` fails.)
If `det(I − T₄Δ) ≠ 0` and `T(Δ) ⪰ 0` for every `Δ ∈ ℝ^{k×l}` with `‖Δ‖ ≤ 1`, then `‖T₄‖ < 1`
and some `τ ≥ 0` makes the block matrix (10) positive semidefinite. -/
theorem lemma22_necessity {d k l : ℕ} (T₁ : Matrix (Fin d) (Fin d) ℝ) (hT₁ : T₁ = T₁ᵀ)
    (T₂ : Matrix (Fin d) (Fin k) ℝ) (T₃ : Matrix (Fin l) (Fin d) ℝ)
    (T₄ : Matrix (Fin l) (Fin k) ℝ) (hT : T₂ ≠ 0 ∨ T₃ = 0)
    (h9 : ∀ Δ : Matrix (Fin k) (Fin l) ℝ, specNorm Δ ≤ 1 →
      (1 - T₄ * Δ).det ≠ 0 ∧ (lftT T₁ T₂ T₃ T₄ Δ).PosSemidef) :
    specNorm T₄ < 1 ∧ ∃ τ : ℝ, 0 ≤ τ ∧ (lemma22Block T₁ T₂ T₃ T₄ τ).PosSemidef := by sorry

end RobustLS.LinFrac
