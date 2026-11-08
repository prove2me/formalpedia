-- Prove2me | Theorems.Thm_ParityCubes_eq_2
-- name    : ParityCubes.eq_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T10:16:15.967461+00:00
-- url     : https://prove2.me/theorems/40453913-b7ee-4e81-94ae-e3879d63ac54
-- title:
--   Eq. (2) — summing over the selectors gives the indicator of the multicolored cliques
-- statement:
--   Let a graph have color classes $V_1,\dots,V_r$, nonempty, with $r\ge 2$. With $A=\{a_1,\dots,a_r\}$,
--
--   $$D_AQ(y)=\bigwedge_{\{u,v\}\text{ incompatible}}(\neg y_u\vee\neg y_v)\cdot\prod_i\Big(\bigvee_{v\in V_i}y_v\Big)=:C_G(y),$$
--
--   and $C_G$ is the indicator of the multicolored cliques: $C_G(y)=1$ exactly when $y$ is the indicator of the vertex set of a multicolored clique.
--
--   So $A$ is a zero cube of $Q$ exactly when there is no multicolored clique, which is the core of the reduction of Theorem 4.1.
--
--   Differences from the source:
--   - encoding: the variables a_i and y_v of Q → the type Fin r ⊕ V, with V an arbitrary finite vertex type and classes the fibres of col : V → Fin r; reason: the same formula; classes numbered from 0
-- source:
--   Sheshadri, Smirnov, The Complexity of Choosing Parity Projections, arXiv:2611.00289 (manuscript sha256 95994d2d…), proof of Theorem 4.1, eq. (2), p.9 (PDF p.10)

import Mathlib
import Definitions.Def_ParityCubes_cubeSum
import Definitions.Def_ParityCubes_selectorFormula

set_option autoImplicit false

namespace ParityCubes

/-- **Eq. (2)** (Sheshadri–Smirnov, arXiv:2611.00289, manuscript sha256 95994d2d…, proof of Theorem
4.1, p.9 (PDF p.10)). For nonempty color classes `V_1, …, V_r`, `r ≥ 2`, summing `Q(a, y)` over all
selectors gives `C_G(y)`, and `C_G` is the indicator of the multicolored cliques: `C_G(y) = 1` exactly
when `y` is the indicator of the vertex set of a multicolored clique. -/
theorem eq_2 {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ} (col : V → Fin r)
    (G : SimpleGraph V) [DecidableRel G.Adj] (hr : 2 ≤ r) (hcol : ∀ i : Fin r, ∃ v : V, col v = i) :
    (∀ y : Fin r ⊕ V → Bool,
      cubeSum (selectorFormula col G) (Finset.univ.image (Sum.inl : Fin r → Fin r ⊕ V)) y =
        cliqueIndicator col G (fun v => y (Sum.inr v))) ∧
    (∀ y : V → Bool, cliqueIndicator col G y = true ↔
      ∃ s : Fin r → V, (∀ i : Fin r, col (s i) = i) ∧
        (∀ i j : Fin r, i ≠ j → G.Adj (s i) (s j)) ∧ ∀ v : V, y v = true ↔ v ∈ Set.range s) := by sorry

end ParityCubes
