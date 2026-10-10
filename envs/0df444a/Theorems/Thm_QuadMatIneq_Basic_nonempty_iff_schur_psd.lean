-- Prove2me | Theorems.Thm_QuadMatIneq_Basic_nonempty_iff_schur_psd
-- name    : QuadMatIneq.Basic.nonempty_iff_schur_psd
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:16:04.79612+00:00
-- url     : https://prove2.me/theorems/889593a6-6864-4ba4-9ca7-ee38ff867817
-- title:
--   §3, p. 6 (after (3.4)) — for Π ∈ 𝕊^{q+r} with Π₂₂ ⩽ 0 and ker Π₂₂ ⊆ ker Π₁₂: 𝒵_r(Π) ≠ ∅ iff Π|Π₂₂ ⩾ 0
-- statement:
--   Let $\Pi \in \mathbb{S}^{q+r}$ be symmetric, partitioned with $\Pi_{11}$ of size $q\times q$ and $\Pi_{22}$ of size $r\times r$, and suppose $\Pi_{22} \le 0$ and $\ker\Pi_{22}\subseteq\ker\Pi_{12}$. Let
--   $$\mathcal Z_r(\Pi) = \Big\{ Z \in \mathbb{R}^{r\times q} : \begin{bmatrix} I_q \\ Z\end{bmatrix}^\top \Pi \begin{bmatrix} I_q \\ Z\end{bmatrix} \ge 0\Big\}.$$
--   Then
--   $$\mathcal Z_r(\Pi) \neq \varnothing \iff \Pi\,|\,\Pi_{22} = \Pi_{11} - \Pi_{12}\Pi_{22}^\dagger\Pi_{21} \ge 0.$$
--
--   This criterion motivates the class $\boldsymbol\Pi_{q,r}$ of (3.5): under the two standing conditions on $\Pi_{22}$ and $\Pi_{12}$, nonemptiness of the solution set is exactly positive semidefiniteness of the Schur complement.
-- source:
--   van Waarde–Camlibel–Eising–Trentelman, arXiv:2203.12959v3, §3, sentence after display (3.4), p. 6

import Mathlib
import Definitions.Def_QuadMatIneq_Basic_QMI

namespace QuadMatIneq.Basic
open Matrix
theorem nonempty_iff_schur_psd {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hP : P.IsHermitian) (h22 : (-P.toBlocks₂₂).PosSemidef)
    (hker : ∀ v : κ → ℝ, P.toBlocks₂₂ *ᵥ v = 0 → P.toBlocks₁₂ *ᵥ v = 0) :
    (ZSet P).Nonempty ↔ (schur P).PosSemidef := by sorry
end QuadMatIneq.Basic
