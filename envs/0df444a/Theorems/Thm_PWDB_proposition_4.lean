-- Prove2me | Theorems.Thm_PWDB_proposition_4
-- name    : PWDB.proposition_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:39:40.629643+00:00
-- url     : https://prove2.me/theorems/c71e5a81-2a0b-44fa-a95a-ccc0f24ccff7
-- title:
--   Proposition 4 — convex reformulation of (P-W)
-- statement:
--   Let $E, F$ be finite-dimensional real inner product spaces, $I$, $L$ finite index sets, $f_0, f_i : E \times F \to \mathbb R$ satisfy (RF) (convex in $x$, concave in $z$), and $c_\ell : F \to \overline{\mathbb R}$ satisfy (C) (proper, closed, convex), with $Z = \{z \mid c_\ell(z) \le 0\ \forall \ell\}$ nonempty.
--
--   1. $\inf(\mathrm{P\text{-}W}) \le \inf(\mathrm{P\text{-}W'})$.
--   2. If $Z$ admits a Slater point, then $\inf(\mathrm{P\text{-}W}) = \inf(\mathrm{P\text{-}W'})$, and (P-W) is solvable if and only if (P-W′) is solvable.
--   3. If $Z$ is compact and (P-W) admits a strict Slater point, then $\inf(\mathrm{P\text{-}W}) = \inf(\mathrm{P\text{-}W'})$, and (P-W) is solvable whenever (P-W′) is solvable.
--
--   In (iii) the solvability of (P-W) does not imply that of (P-W′) (p.12).
--
--   Differences from the source:
--   - generalization: ℝ^{dx}, ℝ^{dz} → finite-dimensional real inner product spaces E, F; reason: every ℝ^d with the dot product is such a space, so the Lean statement specializes to the printed one
--   - encoding: (RF): fi(·, z) proper closed convex, −fi(x, ·) proper closed convex → fi : E → F → ℝ real-valued with IsRF (convex in x, concave in z); reason: p.8 proves (RF) forces real values; a real-valued convex function on a finite-dimensional space is continuous, hence proper and closed; same instances
--   - encoding: (C): cℓ proper, closed and convex, Z nonempty → TensorAHPE.IsProperClosedConvex (c ℓ) with c extended-valued, hypothesis (Z c).Nonempty; reason: standing assumptions of p.9, stated as binders; same instances
--   - encoding: index sets I, L, I0 = {0} ∪ I, L0 = {0} ∪ L → Fintype ι, L (possibly empty), Option ι, Option L with none as the index 0; reason: Lean convention; same instances
--   - encoding: optimal values, feasible regions and solvability of p.40 → EReal ⨅/⨆ over the feasible region; feasibility excludes the bad objective value; Solvable includes the infeasible case; reason: Lean transcription of the conventions stated on p.40; same instances
--   - encoding: convex perspective on ℝ^{dx} × ℝ₊ (Definitions A.2, A.4) → persp/pPersp with value +∞ for t < 0; reason: every multiplier in the paper is ≥ 0; no value at t ≥ 0 changes
--   - reading: Definition 1 (iii): fi(xS) < 0 for every nonlinear fi → fi(xS) < 0 for every fi that is not affine; reason: the paper's conic version, Definition A.6 (p.41), says 'with the exception of those for which fi is affine'; the reading 'not homogeneous linear' would strengthen the hypothesis
-- source:
--   Zhen, Kuhn & Wiesemann, A Unified Theory of Robust and Distributionally Robust Optimization via the Primal-Worst-Equals-Dual-Best Principle, arXiv:2105.00760v2 (19 Jul 2023), Proposition 4, p.11

import Mathlib
import Definitions.Def_TensorAHPE_IsProperClosedConvex
import Definitions.Def_PWDB_IsRF
import Definitions.Def_PWDB_RobustProgram
import Definitions.Def_PWDB_PWPrimeProgram
import Definitions.Def_PWDB_Slater
import Definitions.Def_PWDB_Solvable

namespace PWDB

/-- **Proposition 4 (Convex Reformulation of (P-W))** (Zhen, Kuhn & Wiesemann, arXiv:2105.00760v2,
Proposition 4, p.11): "The following statements hold.
(i) The infimum of (P-W) is smaller or equal to that of (P-W′).
(ii) If Z admits a Slater point, then the infima of (P-W) and (P-W′) coincide, and (P-W) is
solvable if and only if (P-W′) is solvable.
(iii) If Z is compact and (P-W) admits a strict Slater point, then the infima of (P-W) and (P-W′)
coincide, and (P-W) is solvable whenever (P-W′) is solvable."

**Formalization Note** Standing assumptions of §3 (pp.8–9) are binders: (RF) as `IsRF` for real-valued `f0`, `fi`
(p.8 shows (RF) forces real values; on finite-dimensional spaces real-valued convex–concave is
exactly (RF)); (C) as `TensorAHPE.IsProperClosedConvex (c ℓ)` with `c` extended-valued; `Z`
nonempty. `E`, `F` are finite-dimensional real inner product spaces (the paper's `ℝ^{dx}`,
`ℝ^{dz}`), `I`, `L` finite types, possibly empty. Values are in `EReal`; feasible regions exclude
the bad objective value and "solvable" includes the infeasible case (p.40).
A Slater point of `Z` is `SlaterSet c` (Definition 1) with no equality constraints, so affine `cℓ`
may be active. A strict Slater point of (P-W) is `StrictSlaterMin` (Definition 2) for the objective
`sup_{z∈Z} f0(x, z)` and the constraints `sup_{z∈Z} fi(x, z) ≤ 0`. (P-W′) has `I0 = Option ι`,
`L0 = Option L`. Clause (iii) keeps the paper's one direction (p.12: the converse fails). -/
theorem proposition_4 {E F ι L : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [Fintype ι] [Fintype L]
    (c : L → F → EReal) (f₀ : E → F → ℝ) (f : ι → E → F → ℝ)
    (hf₀ : IsRF f₀) (hf : ∀ i, IsRF (f i))
    (hc : ∀ ℓ, TensorAHPE.IsProperClosedConvex (c ℓ)) (hZ : (Z c).Nonempty) :
    pwVal c f₀ f ≤ pwpVal c f₀ f ∧
    ((∃ zS, SlaterSet c (fun e : Empty => e.elim) zS) →
      pwVal c f₀ f = pwpVal c f₀ f ∧
        (SolvableMin (pwFeas c f₀ f) (worst c f₀) ↔
          SolvableMin (pwpFeas c f₀ f) (pwpObj c f₀))) ∧
    (IsCompact (Z c) →
      (∃ xS, StrictSlaterMin (worst c f₀) (fun i => worst c (f i)) (fun e : Empty => e.elim) xS) →
      pwVal c f₀ f = pwpVal c f₀ f ∧
        (SolvableMin (pwpFeas c f₀ f) (pwpObj c f₀) →
          SolvableMin (pwFeas c f₀ f) (worst c f₀))) := by sorry

end PWDB
