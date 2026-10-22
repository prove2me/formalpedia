-- Prove2me | Theorems.Thm_StrategicAlloc_EFXTwoThirds_theorem_4_7
-- name    : StrategicAlloc.EFXTwoThirds.theorem_4_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T15:58:16.460733+00:00
-- url     : https://prove2.me/theorems/4b3794e4-fa6b-46bc-8965-6eac2f5721a7
-- title:
--   Theorem 4.7 — every PNE allocation of an always-EFX two-agent mechanism is α-MMS for some α > 2/3
-- statement:
--   Consider two agents and a fixed finite set $M$ of indivisible goods. Let $\mathcal M$ be a mechanism that maps non-negative bid profiles to allocations of $M$ and that belongs to the class of §4.2: for **every** profile $(v_1,v_2)$ of additive non-negative valuations on $M$, $\mathcal M$ has a pure Nash equilibrium, and every pure Nash equilibrium leads to an allocation that is EFX with respect to $(v_1,v_2)$.
--
--   Then for every valuation profile $(v_1,v_2)$ and every pure Nash equilibrium $\mathbf b$ of $\mathcal M$ under it, there is an $\alpha$ with
--
--   $$\alpha>\tfrac23\qquad\text{and}\qquad v_i(\mathcal M_i(\mathbf b))\ \ge\ \alpha\cdot\mu_i\quad (i=1,2).$$
--
--   By Theorem 2.6 a generic EFX allocation guarantees only $\tfrac23$ of the maximin share, and the bound is tight; equilibria of always-EFX mechanisms therefore separate strictly from the non-strategic worst case.
--
--   **Formalization Note** The number $\alpha$ may depend on the valuation profile and on the equilibrium; the paper claims no uniform $\alpha>\tfrac23$ for the class. The class is a hypothesis: the mechanism allocates all goods on every bid profile (the paper's definition of a mechanism, p. 5), and both "a PNE exists" and "every PNE is EFX" are required for every valuation profile on the same goods. Pure Nash equilibria are measured with the true valuations, and deviations range over all non-negative bid vectors.
-- source:
--   Amanatidis et al., Allocating Indivisible Goods to Strategic Agents, arXiv:2109.08644v2, p. 20, Theorem 4.7

import Mathlib
import Definitions.Def_StrategicAlloc_EFXTwoThirds_Setting

namespace StrategicAlloc.EFXTwoThirds

/-- Theorem 4.7 (p. 20): let `M` be a two-agent mechanism that has a PNE for every valuation
profile and all of whose PNE lead to EFX allocations with respect to the true valuations. Then
the allocation of every PNE of every instance is `α`-MMS for some `α > 2/3` (which may depend on
the instance and the equilibrium). -/
theorem theorem_4_7 {m : ℕ} (M : StrategicAlloc.EFXFour.Mechanism m) (hM : IsAlwaysEFXMechanism M)
    (v : Fin 2 → Fin m → ℝ) (hv : ∀ i g, 0 ≤ v i g)
    (b : Fin 2 → Fin m → ℝ) (hb : IsPNE M v b) :
    ∃ α : ℝ, 2 / 3 < α ∧ StrategicAlloc.EFXFour.IsApproxMMS α v (M b) := by sorry

end StrategicAlloc.EFXTwoThirds
