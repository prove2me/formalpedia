-- Prove2me | Theorems.Thm_PWDB_theorem_6_i_ii
-- name    : PWDB.theorem_6_i_ii
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:39:26.149405+00:00
-- url     : https://prove2.me/theorems/3055a0e7-ee67-412d-bf17-5a71def940e2
-- title:
--   Theorem 6 (i), (ii) — duality between (P-W′) and (D-B′) (assertion (iii) not included)
-- statement:
--   Let $E, F$ be finite-dimensional real inner product spaces, $I$, $L$ finite index sets, $f_0, f_i : E \times F \to \mathbb R$ satisfy (RF) (convex in $x$, concave in $z$), and $c_\ell : F \to \overline{\mathbb R}$ satisfy (C) (proper, closed, convex), with $Z = \{z \mid c_\ell(z) \le 0\ \forall \ell\}$ nonempty.
--
--   1. $\sup(\mathrm{D\text{-}B'}) \le \inf(\mathrm{P\text{-}W'})$.
--   2. If (P-W′) admits a Slater point, then $\inf(\mathrm{P\text{-}W'}) = \sup(\mathrm{D\text{-}B'})$ and (D-B′) is solvable; if (D-B′) admits a Slater point, then $\inf(\mathrm{P\text{-}W'}) = \sup(\mathrm{D\text{-}B'})$ and (P-W′) is solvable.
--
--   Slater points follow Definitions 1–2 on the variable spaces of the two problems; affine constraints ($\sum y = 0$, $\sum w = 0$, $\nu \ge 0$, $\lambda \ge 0$, $c_\ell(z_0) \le 0$ and $\lambda_i c_\ell(\upsilon_i/\lambda_i) \le 0$ for affine $c_\ell$) need not hold strictly. Assertion (iii) of Theorem 6 is a separate statement and is not part of this item.
--
--   Differences from the source:
--   - generalization: ℝ^{dx}, ℝ^{dz} → finite-dimensional real inner product spaces E, F; reason: every ℝ^d with the dot product is such a space, so the Lean statement specializes to the printed one
--   - encoding: (RF): fi(·, z) proper closed convex, −fi(x, ·) proper closed convex → fi : E → F → ℝ real-valued with IsRF (convex in x, concave in z); reason: p.8 proves (RF) forces real values; a real-valued convex function on a finite-dimensional space is continuous, hence proper and closed; same instances
--   - encoding: (C): cℓ proper, closed and convex, Z nonempty → TensorAHPE.IsProperClosedConvex (c ℓ) with c extended-valued, hypothesis (Z c).Nonempty; reason: standing assumptions of p.9, stated as binders; same instances
--   - encoding: index sets I, L, I0 = {0} ∪ I, L0 = {0} ∪ L → Fintype ι, L (possibly empty), Option ι, Option L with none as the index 0; reason: Lean convention; same instances
--   - encoding: optimal values, feasible regions and solvability of p.40 → EReal ⨅/⨆ over the feasible region; feasibility excludes the bad objective value; Solvable includes the infeasible case; reason: Lean transcription of the conventions stated on p.40; same instances
--   - encoding: convex perspective on ℝ^{dx} × ℝ₊ (Definitions A.2, A.4) → persp/pPersp with value +∞ for t < 0; reason: every multiplier in the paper is ≥ 0; no value at t ≥ 0 changes
--   - reading: Definition 1 (iii): fi(xS) < 0 for every nonlinear fi → fi(xS) < 0 for every fi that is not affine; reason: the paper's conic version, Definition A.6 (p.41), says 'with the exception of those for which fi is affine'; the reading 'not homogeneous linear' would strengthen the hypothesis
--   - encoding: vector equations Σ wi = 0 and constraints λ ≥ 0 (ν ≥ 0) in a Slater point (Definition 1) → the scalar linear equations ⟨v, Σ wi⟩ = 0 for all v, and the affine inequalities −λi ≤ 0 (−νiℓ ≤ 0); reason: the same feasible set; all these functions are finite and affine, so conditions (i)–(iii) of Definition 1 are those of the coordinate representation, and strictness gives λ > 0 as in the proof of Proposition C.6 (p.47)
--   - encoding: the joint function (w, z) ↦ fi∗1(w, z) on ℝ^{dx} × ℝ^{dz} and its perspective → jointConj1 on WithLp 2 (E × F); reason: the L² product inner product and topology are those of ℝ^{dx} × ℝ^{dz}, so the conjugate and the perspective are the same
--   - reading: Definition 1 (iii) for the row λi cℓ(υi/λi) ≤ 0 of (D-B′), cℓ affine: on the perspective's domain ℝ^{dz} × ℝ₊ the row is the linear function ⟨a, υi⟩ + bλi → in the Slater point of (D-B′) the row is dbpRow, which extends that linear function to λi < 0, so IsAffineFn holds and the row is exempt from strictness; dbpRow = persp at every λi ≥ 0; reason: the +∞ extension of persp to t < 0 is a Lean convention and must not make a linear row of the paper non-affine; the same feasible set, and a Slater point may have an affine cℓ active
-- source:
--   Zhen, Kuhn & Wiesemann, A Unified Theory of Robust and Distributionally Robust Optimization via the Primal-Worst-Equals-Dual-Best Principle, arXiv:2105.00760v2 (19 Jul 2023), Theorem 6 (i), (ii), p.13

import Mathlib
import Definitions.Def_TensorAHPE_IsProperClosedConvex
import Definitions.Def_PWDB_IsRF
import Definitions.Def_PWDB_RobustProgram
import Definitions.Def_PWDB_PWPrimeProgram
import Definitions.Def_PWDB_DBPrimeProgram
import Definitions.Def_PWDB_Slater
import Definitions.Def_PWDB_Solvable

namespace PWDB

/-- **Theorem 6 (Duality Results for (P-W′) and (D-B′)), assertions (i) and (ii)** (Zhen, Kuhn &
Wiesemann, arXiv:2105.00760v2, Theorem 6, p.13): "The following statements hold.
(i) The infimum of (P-W′) is larger or equal to the supremum of (D-B′).
(ii) If (P-W′) or (D-B′) admits a Slater point, then the infimum of (P-W′) coincides with the
supremum of (D-B′), and (D-B′) or (P-W′) is solvable, respectively."
Assertion (iii) of Theorem 6 is not part of this statement.

**Formalization Note** Standing assumptions of §3 (pp.8–9) are binders: (RF) as `IsRF` for real-valued `f0`, `fi`
(p.8 shows (RF) forces real values; on finite-dimensional spaces real-valued convex–concave is
exactly (RF)); (C) as `TensorAHPE.IsProperClosedConvex (c ℓ)` with `c` extended-valued; `Z`
nonempty. `E`, `F` are finite-dimensional real inner product spaces (the paper's `ℝ^{dx}`,
`ℝ^{dz}`), `I`, `L` finite types, possibly empty. Values are in `EReal`; feasible regions exclude
the bad objective value and "solvable" includes the infeasible case (p.40).
A Slater point of (P-W′) is `SlaterMin` (Definition 2) on its variable space
`E × (I0 → L0 → F) × (I0 → L → ℝ)`, with inequality constraints the `I` rows of (P-W′) and the
affine `−νiℓ ≤ 0` (`pwpIneq`), and the linear equations `Σ_{ℓ∈L0} yiℓ = 0` (`pwpEq`). A Slater
point of (D-B′) is `SlaterMax` on `E × F × (I → E) × (I → F) × (I → ℝ)` with inequality constraints
`cℓ(z0) ≤ 0`, `λi cℓ(υi/λi) ≤ 0` and the affine `−λi ≤ 0` (`dbpIneq`), and the linear equations
`Σ_{i∈I0} wi = 0` (`dbpEq`). Affine constraints are exempt from strictness (Definition 1); this
includes a row `λi cℓ(υi/λi) ≤ 0` with affine `cℓ`, which is linear on the perspective's domain
`ℝ^{dz} × ℝ₊` (`dbpRow`). -/
theorem theorem_6_i_ii {E F ι L : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [Fintype ι] [Fintype L]
    (c : L → F → EReal) (f₀ : E → F → ℝ) (f : ι → E → F → ℝ)
    (hf₀ : IsRF f₀) (hf : ∀ i, IsRF (f i))
    (hc : ∀ ℓ, TensorAHPE.IsProperClosedConvex (c ℓ)) (hZ : (Z c).Nonempty) :
    dbpVal c f₀ f ≤ pwpVal c f₀ f ∧
    ((∃ pS, SlaterMin (pwpObj c f₀) (pwpIneq c f) pwpEq pS) →
      pwpVal c f₀ f = dbpVal c f₀ f ∧ SolvableMax (dbpFeas c f₀ f) (dbpObj f₀ f)) ∧
    ((∃ qS, SlaterMax (dbpObj f₀ f) (dbpIneq c) dbpEq qS) →
      pwpVal c f₀ f = dbpVal c f₀ f ∧ SolvableMin (pwpFeas c f₀ f) (pwpObj c f₀)) := by sorry

end PWDB
