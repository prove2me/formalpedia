-- Prove2me | Theorems.Thm_StrategicAlloc_EFXFour_theorem_4_5
-- name    : StrategicAlloc.EFXFour.theorem_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T14:14:51.917682+00:00
-- url     : https://prove2.me/theorems/ba48dfee-d2b5-47ca-80db-5ab614ac29b8
-- title:
--   Theorem 4.5 — two agents, four goods: every PNE of a mechanism whose PNE always exist and are EFX is MMS
-- statement:
--   Fix a set $M$ of four indivisible goods and two agents. Let $\mathcal M$ be a deterministic mechanism that maps bid profiles $\mathbf b = (\mathbf b_1, \mathbf b_2)$, $\mathbf b_i \in \mathbb R^4_{\ge 0}$, to allocations of $M$, and suppose that, for every profile $(v_1, v_2)$ of additive non-negative valuations on $M$,
--   1. $\mathcal M$ has a pure Nash equilibrium, and
--   2. every pure Nash equilibrium $\mathbf b$ of $\mathcal M$ yields an EFX allocation $\mathcal M(\mathbf b)$ with respect to $(v_1, v_2)$.
--
--   Then every such equilibrium allocation is also an MMS allocation: for every valuation profile $(v_1, v_2)$ and every PNE $\mathbf b$, writing $\mathcal M(\mathbf b) = (A_1, A_2)$,
--   $$
--   v_i(A_i) \ge \mu_i \qquad \text{for } i = 1, 2.
--   $$
--
--   Without incentives, an EFX allocation of two agents only guarantees $\tfrac23$ of the maximin share, and this is tight already with four goods (Theorem 2.6). The theorem shows that EFX allocations arising as equilibria of any always-EFX mechanism are strictly fairer on four goods.
--
--   **Formalization Note** Goods are `Fin 4` and agents `Fin 2`. The class of mechanisms is a hypothesis with all of its clauses: the mechanism allocates all goods on every non-negative bid profile (the paper's definition of a mechanism, p. 5), has a PNE for every non-negative valuation profile on the same four goods, and every PNE is EFX in the sense of Definition 2.1 (only positively valued goods are removed). Best responses range over all non-negative bid vectors, and EFX and MMS are measured with the true valuations.
-- source:
--   Amanatidis et al., Allocating Indivisible Goods to Strategic Agents, arXiv:2109.08644v2, p. 19, Theorem 4.5 (the class of mechanisms: p. 18, §4.2; mechanisms: p. 5, §2.2)

import Mathlib
import Definitions.Def_StrategicAlloc_EFXFour_Setting

namespace StrategicAlloc.EFXFour

theorem theorem_4_5 (M : Mechanism 4) (hM : IsAlwaysEFXMechanism M)
    (v : Fin 2 → Fin 4 → ℝ) (hv : ∀ i g, 0 ≤ v i g)
    (b : Fin 2 → Fin 4 → ℝ) (hb : StrategicAlloc.RRFair.IsPNE M v b) :
    IsApproxMMS 1 v (M b) := by sorry

end StrategicAlloc.EFXFour
