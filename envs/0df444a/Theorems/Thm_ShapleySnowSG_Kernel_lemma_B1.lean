-- Prove2me | Theorems.Thm_ShapleySnowSG_Kernel_lemma_B1
-- name    : ShapleySnowSG.Kernel.lemma_B1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:58:44.853663+00:00
-- url     : https://prove2.me/theorems/f383a40b-24c4-4ef4-995c-4f29990bfbaa
-- title:
--   Lemma B1, p. 28 — det(M + wU) = det(M) + w S(co(M)); S(co(M + wU)), co(M + wU)1 and ᵗco(M + wU)1 do not depend on w
-- statement:
--   Let $M$ be a real square matrix and $U$ the matrix of ones of the same size. Then:
--
--   1. $\det(M+wU)=\det(M)+w\,S(\mathrm{co}(M))$ for all $w\in\mathbb R$;
--   2. the map $w\mapsto S(\mathrm{co}(M+wU))$ is constant;
--   3. the maps $w\mapsto\mathrm{co}(M+wU)\mathbf 1$ and $w\mapsto{}^t\mathrm{co}(M+wU)\mathbf 1$ are constant.
--
--   These identities show that translating a game by a constant does not change its Shapley–Snow kernels or their strategies.
--
--   **Formalization Note** "Constant" is stated as equality with the value at $w=0$. The source prints "$z\mapsto$" in part 3 for the second map; it is read as $w\mapsto$. No invertibility of $M$ is assumed.
-- source:
--   Attia & Oliu-Barton, Shapley–Snow kernels, multiparameter eigenvalue problems and stochastic games, arXiv:1810.08798v2, p. 28, Lemma B1

import Mathlib
import Definitions.Def_ShapleySnowSG_Kernel_MatrixGame

namespace ShapleySnowSG.Kernel

open Matrix

/-- Lemma B1, p. 28: for a square matrix `M` and the matrix of ones `U`:
(i) `det(M + wU) = det(M) + w S(co(M))`; (ii) `w ↦ S(co(M + wU))` is constant;
(iii) `w ↦ co(M + wU) 1` and `w ↦ ᵗco(M + wU) 1` are constant. -/
theorem lemma_B1 {m : Type*} [Fintype m] [DecidableEq m] (M : Matrix m m ℝ) :
    (∀ w : ℝ, (M + w • onesMat m m).det = M.det + w * Ssum (co M)) ∧
    (∀ w : ℝ, Ssum (co (M + w • onesMat m m)) = Ssum (co M)) ∧
    (∀ w : ℝ, co (M + w • onesMat m m) *ᵥ (fun _ => (1 : ℝ)) = co M *ᵥ (fun _ => (1 : ℝ))) ∧
    (∀ w : ℝ, (co (M + w • onesMat m m))ᵀ *ᵥ (fun _ => (1 : ℝ)) =
      (co M)ᵀ *ᵥ (fun _ => (1 : ℝ))) := by sorry

end ShapleySnowSG.Kernel
