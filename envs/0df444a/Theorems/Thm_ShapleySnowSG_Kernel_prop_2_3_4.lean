-- Prove2me | Theorems.Thm_ShapleySnowSG_Kernel_prop_2_3_4
-- name    : ShapleySnowSG.Kernel.prop_2_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:58:47.939972+00:00
-- url     : https://prove2.me/theorems/889fd529-ed1e-404b-b0df-6c5f08136de9
-- title:
--   Proposition 2.3.4, pp. 10–11 — for a kernel Ġ and v = val(G): det(Ġ − vU̇) = 0, Ker = ⟨ẏ⟩, ⟨ẋ⟩, co(Ġ − vU̇) = S(·) ẋ ᵗẏ
-- statement:
--   Let $G$ be a real $I\times J$ matrix game ($I,J$ finite, nonempty) with value $v=\mathrm{val}(G)$, let $\dot G$ be a Shapley–Snow kernel of $G$ corresponding to the basic solution $(x,y)$, and let $\dot x,\dot y$ be the restrictions of $x,y$ to the rows and columns of $\dot G$. Write $U,\dot U$ for matrices of ones. Then:
--
--   1. $S(\mathrm{co}(\dot G-v\dot U))\neq0$;
--   2. $\det(\dot G-v\dot U)=\mathrm{val}(\dot G-v\dot U)=\mathrm{val}(G-vU)=0$;
--   3. $\mathrm{Ker}(\dot G-v\dot U)=\langle\dot y\rangle$ and $\mathrm{Ker}({}^t(\dot G-v\dot U))=\langle\dot x\rangle$;
--   4. $\mathrm{co}(\dot G-v\dot U)=S(\mathrm{co}(\dot G-v\dot U))\,\dot x\,{}^t\dot y$.
--
--   Part 3 provides the nonnegative kernel vectors to which Proposition 2.4.4 is applied in the stochastic game.
--
--   **Formalization Note** The basic solution of the kernel is the one given by its cofactor formulas, so $\dot x$ and $\dot y$ are $\mathrm{co}(\dot G)\mathbf 1/S(\mathrm{co}(\dot G))$ and ${}^t\mathrm{co}(\dot G)\mathbf 1/S(\mathrm{co}(\dot G))$.
-- source:
--   Attia & Oliu-Barton, Shapley–Snow kernels, multiparameter eigenvalue problems and stochastic games, arXiv:1810.08798v2, pp. 10–11, Proposition 2.3.4 (restated and proved pp. 28–30)

import Mathlib
import Definitions.Def_ShapleySnowSG_Kernel_MatrixGame

namespace ShapleySnowSG.Kernel

open Matrix

/-- Proposition 2.3.4, pp. 10–11: let `Ġ` be a Shapley–Snow kernel of `G`, with basic solution
`(x, y)` (restrictions `ẋ`, `ẏ`), and `v = val(G)`. Then (i) `S(co(Ġ − vU̇)) ≠ 0`;
(ii) `det(Ġ − vU̇) = val(Ġ − vU̇) = val(G − vU) = 0`; (iii) `Ker(Ġ − vU̇) = ⟨ẏ⟩` and
`Ker(ᵗ(Ġ − vU̇)) = ⟨ẋ⟩`; (iv) `co(Ġ − vU̇) = S(co(Ġ − vU̇)) ẋ ᵗẏ`. -/
theorem prop_2_3_4 {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
    (G : Matrix ι κ ℝ) (v : ℝ) (hv : IsMatVal G v)
    (s : ℕ) (r : Fin s ↪ ι) (c : Fin s ↪ κ) (hK : IsSSK G s r c) :
    Ssum (co (subGame G s r c - v • onesMat (Fin s) (Fin s))) ≠ 0 ∧
    ((subGame G s r c - v • onesMat (Fin s) (Fin s)).det = 0 ∧
      IsMatVal (subGame G s r c - v • onesMat (Fin s) (Fin s)) 0 ∧
      IsMatVal (G - v • onesMat ι κ) 0) ∧
    (LinearMap.ker (subGame G s r c - v • onesMat (Fin s) (Fin s)).mulVecLin =
        ℝ ∙ ssCol G s r c ∧
      LinearMap.ker (subGame G s r c - v • onesMat (Fin s) (Fin s))ᵀ.mulVecLin =
        ℝ ∙ ssRow G s r c) ∧
    co (subGame G s r c - v • onesMat (Fin s) (Fin s)) =
      Ssum (co (subGame G s r c - v • onesMat (Fin s) (Fin s))) •
        vecMulVec (ssRow G s r c) (ssCol G s r c) := by sorry

end ShapleySnowSG.Kernel
