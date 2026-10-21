-- Prove2me | Theorems.Thm_ShapleySnowSG_Kernel_theorem_2_3_1
-- name    : ShapleySnowSG.Kernel.theorem_2_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:58:47.822807+00:00
-- url     : https://prove2.me/theorems/627443a9-d209-44e3-85d7-3ea97884843b
-- title:
--   Theorem 2.3.1 (Shapley–Snow 1950), p. 10 — basic solutions are exactly the cofactor formulas of square sub-games with S(co(Ġ)) ≠ 0
-- statement:
--   Let $G$ be a real $I\times J$ matrix game ($I,J$ finite, nonempty) and let $X^*\times Y^*$ be its set of optimal strategy pairs. A pair $(x,y)\in X^*\times Y^*$ is a **basic solution** (an extreme point of $X^*\times Y^*$) if and only if there is a square sub-game $\dot G$ of $G$, with rows $\dot I$ and columns $\dot J$, such that
--
--   1. $S(\mathrm{co}(\dot G))\neq0$;
--   2. $\dot x=\dfrac{\mathrm{co}(\dot G)}{S(\mathrm{co}(\dot G))}\mathbf 1$ and $\dot y=\dfrac{{}^t\mathrm{co}(\dot G)}{S(\mathrm{co}(\dot G))}\mathbf 1$, where $\dot x,\dot y$ are the restrictions of $x,y$ to $\dot I,\dot J$.
--
--   In this case moreover
--
--   3. $\mathrm{val}(G)=\mathrm{val}(\dot G)=\dfrac{\det(\dot G)}{S(\mathrm{co}(\dot G))}$;
--   4. ${}^t\dot x\dot G=\mathrm{val}(G)\,{}^t\mathbf 1$ and $\dot G\dot y=\mathrm{val}(G)\,\mathbf 1$.
--
--   This classical description of the extreme optimal strategies is what lets the paper replace each local game by a square sub-game with the same value.
--
--   **Formalization Note** The square sub-game is given by embeddings `r : Fin s ↪ I`, `c : Fin s ↪ J`; $\dot x$ is `fun a => x (r a)`. Part 4 is written with $\det(\dot G)/S(\mathrm{co}(\dot G))$ in place of $\mathrm{val}(G)$, which is the same number by part 3.
-- source:
--   Attia & Oliu-Barton, Shapley–Snow kernels, multiparameter eigenvalue problems and stochastic games, arXiv:1810.08798v2, p. 10, Theorem 2.3.1

import Mathlib
import Definitions.Def_ShapleySnowSG_Kernel_MatrixGame

namespace ShapleySnowSG.Kernel

open Matrix

/-- Theorem 2.3.1 (Shapley and Snow 1950), p. 10: an optimal pair `(x, y) ∈ X* × Y*` is a basic
solution (an extreme point of `X* × Y*`) iff some square sub-game `Ġ` has `S(co(Ġ)) ≠ 0`,
`ẋ = co(Ġ) 1 / S(co(Ġ))` and `ẏ = ᵗco(Ġ) 1 / S(co(Ġ))`; and then
`val(G) = val(Ġ) = det(Ġ) / S(co(Ġ))`, `ᵗẋ Ġ = val(G) ᵗ1` and `Ġ ẏ = val(G) 1`. -/
theorem theorem_2_3_1 {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
    (G : Matrix ι κ ℝ) (x : ι → ℝ) (y : κ → ℝ) (hx : x ∈ optRow G) (hy : y ∈ optCol G) :
    ((x, y) ∈ Set.extremePoints ℝ (optRow G ×ˢ optCol G) ↔
      ∃ (s : ℕ) (r : Fin s ↪ ι) (c : Fin s ↪ κ),
        Ssum (co (subGame G s r c)) ≠ 0 ∧
        (∀ a, x (r a) = ssRow G s r c a) ∧ (∀ b, y (c b) = ssCol G s r c b)) ∧
    (∀ (s : ℕ) (r : Fin s ↪ ι) (c : Fin s ↪ κ),
      Ssum (co (subGame G s r c)) ≠ 0 →
      (∀ a, x (r a) = ssRow G s r c a) → (∀ b, y (c b) = ssCol G s r c b) →
      IsMatVal G ((subGame G s r c).det / Ssum (co (subGame G s r c))) ∧
      IsMatVal (subGame G s r c) ((subGame G s r c).det / Ssum (co (subGame G s r c))) ∧
      (fun a => x (r a)) ᵥ* subGame G s r c =
        (fun _ => (subGame G s r c).det / Ssum (co (subGame G s r c))) ∧
      subGame G s r c *ᵥ (fun b => y (c b)) =
        (fun _ => (subGame G s r c).det / Ssum (co (subGame G s r c)))) := by sorry

end ShapleySnowSG.Kernel
