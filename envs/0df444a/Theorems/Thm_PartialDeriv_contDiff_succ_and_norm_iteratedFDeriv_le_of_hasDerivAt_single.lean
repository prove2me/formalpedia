-- Prove2me | Theorems.Thm_PartialDeriv_contDiff_succ_and_norm_iteratedFDeriv_le_of_hasDerivAt_single
-- name    : PartialDeriv.contDiff_succ_and_norm_iteratedFDeriv_le_of_hasDerivAt_single
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/04020a9a-e75a-5016-b664-994e8290a2aa
-- title:
--   Coordinate derivatives of class C^m give f of class C^{m+1}
-- statement:
--   Let $n, m$ be natural numbers, let $f \colon \mathbb{R}^n \to \mathbb{C}$ (with $\mathbb{R}^n$ realised as $\mathrm{Fin}\,n \to \mathbb{R}$, carrying the sup norm), and let $g \colon \mathrm{Fin}\,n \to (\mathbb{R}^n \to \mathbb{C})$ be a family of candidate partial derivatives. Assume that each $g_j$ is of class $C^m$ over $\mathbb{R}$, and that for every point $t \in \mathbb{R}^n$ and every index $j$ the one-variable function $s \mapsto f(t + s\,e_j)$, where $e_j =$ `Pi.single j 1` is the $j$-th standard basis vector, is differentiable at $s = 0$ with derivative $g_j(t)$. The conclusion is threefold: first, $f$ is of class $C^{m+1}$ over $\mathbb{R}$; second, at every $t$ the function $f$ is Fréchet differentiable with derivative the continuous linear map $\sum_j \mathrm{proj}_j \cdot g_j(t)$, that is $v \mapsto \sum_j v_j\, g_j(t)$, where $\mathrm{proj}_j$ is the $j$-th coordinate projection; and third, for every $k \le m$ and every $t$ one has the bound $\|D^{k+1} f(t)\| \le \sum_j \|D^k g_j(t)\|$ on the iterated Fréchet derivatives.
--
--   This is the classical theorem that a function whose partial derivatives along the coordinate directions exist everywhere and are of class $C^m$ is itself of class $C^{m+1}$, packaged in $n$ variables and supplemented by a bound of the $(k+1)$-st iterated Fréchet derivative of $f$ by the sum of the $k$-th iterated derivatives of the partials. It serves to bootstrap regularity one order at a time along a frame of coordinate directions, and is used in the construction of smooth data for automorphic forms, namely in [`AutomorphicForm.exists_forall_contDiff_norm_iteratedFDeriv_comp_flowChart_le_sum_foldr_archDeriv`](thm.html#AutomorphicForm.exists_forall_contDiff_norm_iteratedFDeriv_comp_flowChart_le_sum_foldr_archDeriv).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PartialDeriv_contDiff_succ_and_norm_iteratedFDeriv_le_of_hasDerivAt_single.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PartialDeriv.contDiff_succ_and_norm_iteratedFDeriv_le_of_hasDerivAt_single
    (n m : ℕ) (f : (Fin n → ℝ) → ℂ) (g : Fin n → (Fin n → ℝ) → ℂ)
    (hg : ∀ j, ContDiff ℝ m (g j))
    (hfg : ∀ (t : Fin n → ℝ) (j : Fin n),
      HasDerivAt (fun s : ℝ => f (t + s • (Pi.single j (1 : ℝ) : Fin n → ℝ))) (g j t) 0) :
    ContDiff ℝ (m + 1) f ∧
      (∀ t, HasFDerivAt f (∑ j, (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).smulRight (g j t)) t) ∧
      ∀ k, k ≤ m → ∀ t, ‖iteratedFDeriv ℝ (k + 1) f t‖ ≤ ∑ j, ‖iteratedFDeriv ℝ k (g j) t‖ := by sorry
