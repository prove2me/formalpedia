-- Prove2me | Theorems.Thm_PWDB_theorem_3
-- name    : PWDB.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:39:10.936363+00:00
-- url     : https://prove2.me/theorems/32fea5dc-7bce-43ff-bc00-446385454f28
-- title:
--   Theorem 3 — weak duality between (P-W) and (D-B)
-- statement:
--   Let $E, F$ be finite-dimensional real inner product spaces, $I$, $L$ finite index sets, $f_0, f_i : E \times F \to \mathbb R$ satisfy (RF) (convex in $x$, concave in $z$), and $c_\ell : F \to \overline{\mathbb R}$ satisfy (C) (proper, closed, convex), with $Z = \{z \mid c_\ell(z) \le 0\ \forall \ell\}$ nonempty.
--
--   Then the infimum of the primal worst problem is at least the supremum of the dual best problem:
--   $$
--   \sup\,(\mathrm{D\text{-}B}) \le \inf\,(\mathrm{P\text{-}W}).
--   $$
--
--   Differences from the source:
--   - generalization: ℝ^{dx}, ℝ^{dz} → finite-dimensional real inner product spaces E, F; reason: every ℝ^d with the dot product is such a space, so the Lean statement specializes to the printed one
--   - encoding: (RF): fi(·, z) proper closed convex, −fi(x, ·) proper closed convex → fi : E → F → ℝ real-valued with IsRF (convex in x, concave in z); reason: p.8 proves (RF) forces real values; a real-valued convex function on a finite-dimensional space is continuous, hence proper and closed; same instances
--   - encoding: (C): cℓ proper, closed and convex, Z nonempty → TensorAHPE.IsProperClosedConvex (c ℓ) with c extended-valued, hypothesis (Z c).Nonempty; reason: standing assumptions of p.9, stated as binders; same instances
--   - encoding: index sets I, L, I0 = {0} ∪ I, L0 = {0} ∪ L → Fintype ι, L (possibly empty), Option ι, Option L with none as the index 0; reason: Lean convention; same instances
--   - encoding: optimal values, feasible regions and solvability of p.40 → EReal ⨅/⨆ over the feasible region; feasibility excludes the bad objective value; Solvable includes the infeasible case; reason: Lean transcription of the conventions stated on p.40; same instances
--   - encoding: convex perspective on ℝ^{dx} × ℝ₊ (Definitions A.2, A.4) → persp/pPersp with value +∞ for t < 0; reason: every multiplier in the paper is ≥ 0; no value at t ≥ 0 changes
-- source:
--   Zhen, Kuhn & Wiesemann, A Unified Theory of Robust and Distributionally Robust Optimization via the Primal-Worst-Equals-Dual-Best Principle, arXiv:2105.00760v2 (19 Jul 2023), Theorem 3, p.10; standing assumptions (RF), (C) and eq. (1), pp.8–9

import Mathlib
import Definitions.Def_TensorAHPE_IsProperClosedConvex
import Definitions.Def_PWDB_IsRF
import Definitions.Def_PWDB_RobustProgram

namespace PWDB

/-- **Theorem 3 (Weak Duality for (P-W) and (D-B))** (Zhen, Kuhn & Wiesemann, arXiv:2105.00760v2,
Theorem 3, p.10): "The infimum of the primal worst problem (P-W) is larger or equal to the supremum
of the dual best problem (D-B)."

**Formalization Note** Standing assumptions of §3 (pp.8–9) are binders: (RF) as `IsRF` for real-valued `f0`, `fi`
(p.8 shows (RF) forces real values; on finite-dimensional spaces real-valued convex–concave is
exactly (RF)); (C) as `TensorAHPE.IsProperClosedConvex (c ℓ)` with `c` extended-valued; `Z`
nonempty. `E`, `F` are finite-dimensional real inner product spaces (the paper's `ℝ^{dx}`,
`ℝ^{dz}`), `I`, `L` finite types, possibly empty. Values are in `EReal`; feasible regions exclude
the bad objective value and "solvable" includes the infeasible case (p.40). -/
theorem theorem_3 {E F ι L : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [Fintype ι] [Fintype L]
    (c : L → F → EReal) (f₀ : E → F → ℝ) (f : ι → E → F → ℝ)
    (hf₀ : IsRF f₀) (hf : ∀ i, IsRF (f i))
    (hc : ∀ ℓ, TensorAHPE.IsProperClosedConvex (c ℓ)) (hZ : (Z c).Nonempty) :
    dbVal c f₀ f ≤ pwVal c f₀ f := by sorry

end PWDB
