-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_epsSubgrad_of_subgrad_active_piece
-- name    : QAlgorithms.Nannicini.epsSubgrad_of_subgrad_active_piece
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-13T17:53:28.453716+00:00
-- url     : https://prove2.me/theorems/885ca32a-29df-4d22-88cb-33004893ddaa
-- title:
--   A subgradient of the active piece at a nearby point is an approximate subgradient of the max
-- statement:
--   Let $E$ be a real normed space and let $h_1,\dots,h_m:E\to\mathbb R$ be convex and $1$-Lipschitz; put $f(x)=\max_{i}h_i(x)$. Let $\epsilon\in\mathbb R$ and $\bar x,\hat x\in E$ with $\|\bar x-\hat x\|\le\epsilon/4$, and let $j$ be an index with $h_i(\hat x)\le h_j(\hat x)$ for all $i$. If $g\in E^*$ is a subgradient of $h_j$ at $\hat x$, i.e. $h_j(x)\ge h_j(\hat x)+\langle g,x-\hat x\rangle$ for all $x\in E$, then $g$ is an $\hat\epsilon$-subgradient of $f$ at $\bar x$:
--
--   $$f(x)\ \ge\ f(\bar x)+\langle g,x-\bar x\rangle-\hat\epsilon\quad\text{for all }x\in E,\qquad \hat\epsilon=\frac{\epsilon}{4}\big(\|g\|_*+1\big),$$
--
--   where $\|g\|_*=\sup_{\|x\|=1}\langle g,x\rangle$ is the dual norm.
--
--   The lemma is the device by which a subgradient computed at an estimated point certifies an approximate subgradient at the true iterate.
--
--   **Formalization Note** The dual space is the space of continuous linear functionals and the dual norm is the operator norm.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 201, Lemma 8.29. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_SDP
import Definitions.Def_QAlgorithms_Nannicini_Ch08b_Model
set_option autoImplicit false

namespace QAlgorithms.Nannicini

open QAlgorithms.SDP


/-- Nannicini p.201, Lemma 8.29. Let `h_1, …, h_m` be 1-Lipschitz convex functions and
`f(x) = max_i h_i(x)`. For points `x̄, x̂` with `‖x̄ − x̂‖ ≤ ϵ/4`, let `j ∈ argmax_i h_i(x̂)`. Then,
for `g ∈ ∂h_j(x̂)`, we have `g ∈ ∂_{ϵ̂} f(x̄)`, where `ϵ̂ = (ϵ/4)(‖g‖_* + 1)`.

The space is any real normed space `E` (in Prop. 8.28 it is the space of Hermitian matrices with
the trace norm). Subgradients are elements of the dual `E*` (Def. 5.24), here continuous linear
functionals, and the dual norm `‖g‖_* = max_{‖x‖=1} ⟨g, x⟩` (Def. 8.4, p.181) is the operator norm
of `g`. The index `j` is in the argmax: `h_i(x̂) ≤ h_j(x̂)` for all `i`; the maximum over the
(nonempty, since `j` exists) index set is `Finset.sup'`. -/
theorem epsSubgrad_of_subgrad_active_piece {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : ℕ} (h : Fin m → E → ℝ) (hLip : ∀ i, LipschitzWith 1 (h i))
    (hconv : ∀ i, ConvexOn ℝ Set.univ (h i)) (ε : ℝ) (xbar xhat : E)
    (hdist : ‖xbar - xhat‖ ≤ ε * 4⁻¹) (j : Fin m) (hj : ∀ i, h i xhat ≤ h j xhat)
    (g : E →L[ℝ] ℝ) (hg : IsEpsSubgradOn Set.univ (h j) 0 xhat g.toLinearMap) :
    IsEpsSubgradOn Set.univ
      (fun x => Finset.univ.sup' ⟨j, Finset.mem_univ j⟩ fun i => h i x)
      (ε * 4⁻¹ * (‖g‖ + 1)) xbar g.toLinearMap := by
  sorry



















end QAlgorithms.Nannicini
