-- Prove2me | Theorems.Thm_TwinWidthI_GridThm_theorem_5_4
-- name    : TwinWidthI.GridThm.theorem_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:44:14.439499+00:00
-- url     : https://prove2.me/theorems/c2e3812e-f293-4c45-b7f1-71d6b3fb98eb
-- title:
--   Theorem 5.4 (Grid Minor Theorem for Twin-width) — t-twin-ordered ⇒ (2t+2)-mixed free; t-mixed free ⇒ tww ≤ 4c_tα^{4c_t+2}
-- statement:
--   Let $M$ be an $n\times m$ matrix with $n,m\ge1$ whose entries come from a finite alphabet of size $\alpha$, let $t\ge0$, and let $c_t=\tfrac83(t+1)^22^{4t}$. Then
--
--   1. if $M$ is $t$-twin-ordered, then $M$ is $(2t+2)$-mixed free;
--   2. if $t\ge1$ and $M$ is $t$-mixed free, then $$\operatorname{tww}(M)\ \le\ 4c_t\,\alpha^{4c_t+2}.$$
--
--   Together the two items say that, up to reordering rows and columns, bounded twin-width is the same as the absence of large mixed minors. The second item is the tool the paper uses to bound twin-width of concrete classes (permutations avoiding a pattern, posets of bounded width, $K_t$-minor free graphs): find an order in which the adjacency matrix has no $t$-mixed minor and apply the theorem.
--
--   **Formalization Note** Twin-width is the partition form `MatTwinWidthLE` (p. 3:18). Since $c_t$ is not an integer, $\alpha^{4c_t+2}$ is a real power and the integer twin-width bound is $\lfloor 4c_t\alpha^{4c_t+2}\rfloor$. The paper's remark "$=2^{2^{O(t)}}$" is not formalized. Added hypotheses: $n,m\ge1$ (a contraction sequence acts on rows and columns), and $t\ge1$ in the second item only: for $t=0$ no $(0,0)$-division of a non-empty matrix exists, so every non-empty matrix is $0$-mixed free and the bound $4c_0\alpha^{4c_0+2}$ would fail for large random matrices.
-- source:
--   Bonnet, Kim, Thomassé and Watrigant, Twin-width I: Tractable FO Model Checking, J. ACM 69(1), Article 3 (2021), p. 3:19, Theorem 5.4

import Mathlib
import Definitions.Def_TwinWidthI_GridThm_Setting

namespace TwinWidthI.GridThm

/-- Theorem 5.4 (Grid Minor Theorem for Twin-width), p. 3:19. Let `α` be the alphabet size and
`c_t = 8/3 (t+1)^2 2^{4t}`. Every `t`-twin-ordered matrix is `(2t + 2)`-mixed free, and every
`t`-mixed free matrix has twin-width at most `4 c_t α^{4 c_t + 2}`. -/
theorem theorem_5_4 {A : Type*} [Fintype A] [DecidableEq A] (n m t : ℕ) (hn : 1 ≤ n)
    (hm : 1 ≤ m) (M : Matrix (Fin n) (Fin m) A) :
    (TwinOrdered M t → MixedFree M (2 * t + 2)) ∧
    (1 ≤ t → MixedFree M t →
      MatTwinWidthLE M ⌊4 * cMT t * (Fintype.card A : ℝ) ^ (4 * cMT t + 2)⌋₊) := by sorry

end TwinWidthI.GridThm
