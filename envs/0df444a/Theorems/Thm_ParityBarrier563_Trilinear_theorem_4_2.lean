-- Prove2me | Theorems.Thm_ParityBarrier563_Trilinear_theorem_4_2
-- name    : ParityBarrier563.Trilinear.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:10:34.438322+00:00
-- url     : https://prove2.me/theorems/9c73223c-4d18-4ac2-8edc-80f558dcf558
-- title:
--   Theorem 4.2 — every b-CNF is a sum of at most 2^{κ|V|} functions cl_b(S) with short point lists
-- statement:
--   Let $V$ be a finite set of variables, $b\ge1$ an integer and $0<\kappa\le1$. Every $b$-CNF $H$ on $\{0,1\}^V$ can be written as
--
--   $$H=\sum_{i=1}^{m}\mathrm{cl}_b(S_i)\qquad\text{pointwise on }\{0,1\}^V,\qquad m\le 2^{\kappa|V|},$$
--
--   where each $S_i$ is a set of satisfying assignments of $H$ with
--
--   $$|S_i|\le 2^{K\,b\log_2(2/\kappa)/\kappa}\,\log_2(2|V|+2),$$
--
--   and $K>0$ is an absolute constant. Since the summands take values in $\{0,1\}$ and add up to the $\{0,1\}$-valued $H$, they accept pairwise disjoint sets of points. An identically false $H$ is the empty sum ($m=0$).
--
--   This decomposition is the main new ingredient of the paper: it replaces sparsification, and its short descriptions make the union bound of Corollary 4.3 affordable at width $b=\Theta(\log n)$.
--
--   Differences from the source:
--   - encoding: a sum of at most 2^{κ|V|} functions cl_b(S) with |S| ≤ 2^{O(b log(2/κ)/κ)} log(2|V|+2) → m ≤ 2^{κ|V|} pieces indexed by Fin m, the identity of real indicators at every point, and ∃ K > 0 chosen before V, b, κ and H with |S_i| ≤ 2^{K·b·log₂(2/κ)/κ}·log₂(2|V|+2); reason: b log₂(2/κ)/κ ≥ 1 on the stated domain, so an additive constant in the O-term is absorbed by K
-- source:
--   Nikolai Chukhin, Xin Li, Ivan Mihajlin, Yan Zhong, Breaking the Parity Barrier for Constant-Depth Circuits, STOC 2027 submission #563 (October 2026), SHA-256 e50e7ff9480ef7c23095e91345faf20f73773bc111e3b0eed2da71a28f7f9462, Theorem 4.2, printed p.14 (PDF p.16)

import Mathlib
import Definitions.Def_ParityBarrier563_Trilinear_Correlation

set_option autoImplicit false

namespace ParityBarrier563.Trilinear

/-- Theorem 4.2, printed p.14 / PDF 16. -/
theorem theorem_4_2 :
    ∃ K : ℝ, 0 < K ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (b : ℕ) (κ : ℝ) (H : BoolFn V),
        1 ≤ b → 0 < κ → κ ≤ 1 → IsCNF b H →
        ∃ (m : ℕ) (S : Fin m → Finset (V → Bool)),
          (m : ℝ) ≤ (2 : ℝ) ^ (κ * Fintype.card V) ∧
          (∀ i, ∀ x ∈ S i, H x = true) ∧
          (∀ i, ((S i).card : ℝ) ≤
            (2 : ℝ) ^ (K * ((b : ℝ) * Real.logb 2 (2 / κ) / κ)) *
              Real.logb 2 (2 * Fintype.card V + 2)) ∧
          ∀ x, ind H x = ∑ i, ind (closure b (S i)) x := by sorry

end ParityBarrier563.Trilinear
