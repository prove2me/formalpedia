-- Prove2me | Theorems.Thm_QuadMatIneq_Basic_theorem_3_2_b
-- name    : QuadMatIneq.Basic.theorem_3_2_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:16:18.786711+00:00
-- url     : https://prove2.me/theorems/c2551ea8-bab6-436a-b59d-7887d0ce1c03
-- title:
--   Theorem 3.2(b), p. 7 — for Π ∈ 𝚷_{q,r} (q ⩾ 1), 𝒵_r(Π) is bounded iff Π₂₂ < 0
-- statement:
--   Let $q \ge 1$, $r \ge 0$, and let $\Pi \in \boldsymbol\Pi_{q,r}$, that is, $\Pi \in \mathbb S^{q+r}$ is symmetric with $\Pi_{22}\le 0$, $\Pi\,|\,\Pi_{22}\ge 0$ and $\ker\Pi_{22}\subseteq\ker\Pi_{12}$. Then the solution set
--   $$\mathcal Z_r(\Pi) = \Big\{ Z \in \mathbb{R}^{r\times q} : \begin{bmatrix} I_q \\ Z\end{bmatrix}^\top \Pi \begin{bmatrix} I_q \\ Z\end{bmatrix} \ge 0\Big\}$$
--   is bounded if and only if
--   $$\Pi_{22} < 0 .$$
--
--   Boundedness of the set of noise-consistent matrices is what makes data-based uncertainty sets compact; this part identifies it with negative definiteness of a single block.
--
--   **Formalization Note.** "Bounded" is stated entrywise: there is $C$ with $|Z_{ij}| \le C$ for all $Z \in \mathcal Z_r(\Pi)$ and all $i, j$; all norms on $\mathbb R^{r\times q}$ are equivalent, so this is the paper's notion. The hypothesis $q \ge 1$ (`Nonempty ι`) is added: for $q = 0$ the space $\mathbb{R}^{r\times 0}$ is a single point, so the set is always bounded while $\Pi_{22}$ may be singular (e.g. $r = 1$, $\Pi = 0$). The paper's proof uses a nonzero vector of $\mathbb R^q$ at exactly this point.
-- source:
--   van Waarde–Camlibel–Eising–Trentelman, arXiv:2203.12959v3, Theorem 3.2(b), p. 7

import Mathlib
import Definitions.Def_QuadMatIneq_Basic_QMI

namespace QuadMatIneq.Basic
open Matrix
theorem theorem_3_2_b {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] [Nonempty ι]
    (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hP : InPi P) :
    (∃ C : ℝ, ∀ Z ∈ ZSet P, ∀ i j, |Z i j| ≤ C) ↔ (-P.toBlocks₂₂).PosDef := by sorry
end QuadMatIneq.Basic
