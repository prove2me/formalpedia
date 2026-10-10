-- Prove2me | Theorems.Thm_QuadMatIneq_Basic_theorem_3_2
-- name    : QuadMatIneq.Basic.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:16:09.747122+00:00
-- url     : https://prove2.me/theorems/e125dfe6-7b32-447b-84ce-23a599e65dd6
-- title:
--   Theorem 3.2, pp. 6–7 — for Π ∈ 𝚷_{q,r}: 𝒵_r(Π) nonempty, convex; bounded iff Π₂₂ < 0; interior iff Π₂₂ = 0 or Π|Π₂₂ > 0; 𝒵⁺ ≠ ∅ iff Π|Π₂₂ > 0; 𝒵⁰ ≠ ∅ iff rank condition
-- statement:
--   Let $q, r \ge 0$ and let $\Pi \in \boldsymbol\Pi_{q,r}$: $\Pi = \begin{bmatrix}\Pi_{11} & \Pi_{12}\\ \Pi_{21} & \Pi_{22}\end{bmatrix} \in \mathbb S^{q+r}$ is symmetric, with $\Pi_{11}$ of size $q\times q$ and $\Pi_{22}$ of size $r\times r$, and
--   $$\Pi_{22} \le 0,\qquad \Pi\,|\,\Pi_{22} := \Pi_{11} - \Pi_{12}\Pi_{22}^\dagger\Pi_{21} \ge 0,\qquad \ker\Pi_{22}\subseteq\ker\Pi_{12},$$
--   where $\Pi_{22}^\dagger$ is the Moore–Penrose pseudo-inverse. For $Z \in \mathbb{R}^{r\times q}$ write $F_\Pi(Z) = \begin{bmatrix} I_q \\ Z\end{bmatrix}^\top \Pi \begin{bmatrix} I_q \\ Z\end{bmatrix}$, and let $\mathcal Z_r(\Pi) = \{Z : F_\Pi(Z)\ge 0\}$, $\mathcal Z_r^+(\Pi) = \{Z : F_\Pi(Z) > 0\}$, $\mathcal Z_r^0(\Pi) = \{Z : F_\Pi(Z) = 0\}$. Then:
--
--   1. (a) $\mathcal Z_r(\Pi)$ is nonempty and convex;
--   2. (b) if $q \ge 1$, $\mathcal Z_r(\Pi)$ is bounded if and only if $\Pi_{22} < 0$;
--   3. (c) $\mathcal Z_r(\Pi)$ has nonempty interior if and only if $\Pi_{22} = 0$ or $\Pi\,|\,\Pi_{22} > 0$;
--   4. (d) $\mathcal Z_r^+(\Pi)$ is nonempty if and only if $\Pi\,|\,\Pi_{22} > 0$;
--   5. (e) $\mathcal Z_r^0(\Pi)$ is nonempty if and only if $\operatorname{rank}\Pi_{22} \ge \operatorname{rank}(\Pi\,|\,\Pi_{22})$.
--
--   These are the basic properties of the solution sets of quadratic matrix inequalities. In data-driven control the set $\mathcal Z_r(\Pi)$ describes all system matrices consistent with noisy data, and the theorem characterizes, purely in terms of the blocks of $\Pi$, when this set is nonempty, bounded, has interior, or contains strict and boundary solutions.
--
--   **Formalization Note.** "Bounded" is entrywise boundedness ($\exists C$ with $|Z_{ij}|\le C$ on the set), equivalent to boundedness in any norm; the interior is taken in $\mathbb R^{r\times q}$ with its Euclidean topology. Part (b) carries the added hypothesis $q \ge 1$ (`Nonempty ι`): for $q = 0$ the space $\mathbb R^{r\times 0}$ is a point, the set is bounded, and $\Pi_{22}$ may still be singular, so (b) as printed fails; the paper's proof picks a nonzero vector of $\mathbb R^q$. Parts (a), (c), (d), (e) are stated without it, and hold for $q = 0$ and $r = 0$.
-- source:
--   van Waarde–Camlibel–Eising–Trentelman, arXiv:2203.12959v3, Theorem 3.2, pp. 6–7

import Mathlib
import Definitions.Def_QuadMatIneq_Basic_QMI

namespace QuadMatIneq.Basic
open Matrix
theorem theorem_3_2 {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hP : InPi P) :
    -- (a) nonempty and convex
    ((ZSet P).Nonempty ∧ Convex ℝ (ZSet P)) ∧
    -- (b) bounded iff Π₂₂ < 0 (for q ⩾ 1)
    (Nonempty ι → ((∃ C : ℝ, ∀ Z ∈ ZSet P, ∀ i j, |Z i j| ≤ C) ↔ (-P.toBlocks₂₂).PosDef)) ∧
    -- (c) nonempty interior iff Π₂₂ = 0 or Π|Π₂₂ > 0
    ((interior (ZSet P)).Nonempty ↔ P.toBlocks₂₂ = 0 ∨ (schur P).PosDef) ∧
    -- (d) 𝒵_r^+(Π) nonempty iff Π|Π₂₂ > 0
    ((ZPlus P).Nonempty ↔ (schur P).PosDef) ∧
    -- (e) 𝒵_r^0(Π) nonempty iff rank Π₂₂ ⩾ rank Π|Π₂₂
    ((ZZero P).Nonempty ↔ (schur P).rank ≤ P.toBlocks₂₂.rank) := by sorry
end QuadMatIneq.Basic
