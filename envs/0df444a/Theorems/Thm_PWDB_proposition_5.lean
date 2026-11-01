-- Prove2me | Theorems.Thm_PWDB_proposition_5
-- name    : PWDB.proposition_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:39:38.104457+00:00
-- url     : https://prove2.me/theorems/34baaeed-3545-4bd2-82d0-680e65ae2764
-- title:
--   Proposition 5 — convex reformulation of (D-B)
-- statement:
--   Let $E, F$ be finite-dimensional real inner product spaces, $I$, $L$ finite index sets, $f_0, f_i : E \times F \to \mathbb R$ satisfy (RF) (convex in $x$, concave in $z$), and $c_\ell : F \to \overline{\mathbb R}$ satisfy (C) (proper, closed, convex), with $Z = \{z \mid c_\ell(z) \le 0\ \forall \ell\}$ nonempty.
--
--   1. $\sup(\mathrm{D\text{-}B}) \le \sup(\mathrm{D\text{-}B'})$.
--   2. If (D-B) admits a strict Slater point, then $\sup(\mathrm{D\text{-}B}) = \sup(\mathrm{D\text{-}B'})$, and (D-B′) is solvable whenever (D-B) is solvable.
--   3. If $Z$ is bounded, then $\sup(\mathrm{D\text{-}B}) = \sup(\mathrm{D\text{-}B'})$, and (D-B′) is solvable if and only if (D-B) is solvable.
--
--   In (ii) the solvability of (D-B′) does not imply that of (D-B) (p.13). Unlike earlier results, (ii) needs no compactness of $Z$.
--
--   Differences from the source:
--   - generalization: ℝ^{dx}, ℝ^{dz} → finite-dimensional real inner product spaces E, F; reason: every ℝ^d with the dot product is such a space, so the Lean statement specializes to the printed one
--   - encoding: (RF): fi(·, z) proper closed convex, −fi(x, ·) proper closed convex → fi : E → F → ℝ real-valued with IsRF (convex in x, concave in z); reason: p.8 proves (RF) forces real values; a real-valued convex function on a finite-dimensional space is continuous, hence proper and closed; same instances
--   - encoding: (C): cℓ proper, closed and convex, Z nonempty → TensorAHPE.IsProperClosedConvex (c ℓ) with c extended-valued, hypothesis (Z c).Nonempty; reason: standing assumptions of p.9, stated as binders; same instances
--   - encoding: index sets I, L, I0 = {0} ∪ I, L0 = {0} ∪ L → Fintype ι, L (possibly empty), Option ι, Option L with none as the index 0; reason: Lean convention; same instances
--   - encoding: optimal values, feasible regions and solvability of p.40 → EReal ⨅/⨆ over the feasible region; feasibility excludes the bad objective value; Solvable includes the infeasible case; reason: Lean transcription of the conventions stated on p.40; same instances
--   - encoding: convex perspective on ℝ^{dx} × ℝ₊ (Definitions A.2, A.4) → persp/pPersp with value +∞ for t < 0; reason: every multiplier in the paper is ≥ 0; no value at t ≥ 0 changes
--   - generalization: strict Slater point of (D-B) (Definition 2: point in ri(dom(−objective)) in the variables (w, z, λ)) → StrictSlaterDB: feasible, λ > 0, cℓ(zi) < 0 and zi ∈ ri dom cℓ, (w0, z0) ∈ ri dom f0∗1, (wi/λi, zi) ∈ ri dom fi∗1; reason: the literal condition implies StrictSlaterDB (the slice of dom(−objective) at fixed λi > 0 is the image of dom fi∗1 under (w, z) ↦ (λi w, z)); the literal ri can be empty (f0 = x, f1 = zx − 1, Z = ℝ), which would make the clause vacuous; StrictSlaterDB is what the proof on p.55 uses
--   - encoding: the joint function (w, z) ↦ fi∗1(w, z) on ℝ^{dx} × ℝ^{dz} and its perspective → jointConj1 on WithLp 2 (E × F); reason: the L² product inner product and topology are those of ℝ^{dx} × ℝ^{dz}, so the conjugate and the perspective are the same
-- source:
--   Zhen, Kuhn & Wiesemann, A Unified Theory of Robust and Distributionally Robust Optimization via the Primal-Worst-Equals-Dual-Best Principle, arXiv:2105.00760v2 (19 Jul 2023), Proposition 5, p.12

import Mathlib
import Definitions.Def_TensorAHPE_IsProperClosedConvex
import Definitions.Def_PWDB_IsRF
import Definitions.Def_PWDB_RobustProgram
import Definitions.Def_PWDB_DBPrimeProgram
import Definitions.Def_PWDB_StrictSlaterDB
import Definitions.Def_PWDB_Solvable

namespace PWDB

/-- **Proposition 5 (Convex Reformulation of (D-B))** (Zhen, Kuhn & Wiesemann, arXiv:2105.00760v2,
Proposition 5, p.12): "The following statements hold.
(i) The supremum of (D-B) is smaller or equal to that of (D-B′).
(ii) If (D-B) admits a strict Slater point, then the suprema of (D-B) and (D-B′) coincide, and
(D-B′) is solvable whenever (D-B) is solvable.
(iii) If Z is bounded, then the suprema of (D-B) and (D-B′) coincide, and (D-B′) is solvable if and
only if (D-B) is solvable."

**Formalization Note** Standing assumptions of §3 (pp.8–9) are binders: (RF) as `IsRF` for real-valued `f0`, `fi`
(p.8 shows (RF) forces real values; on finite-dimensional spaces real-valued convex–concave is
exactly (RF)); (C) as `TensorAHPE.IsProperClosedConvex (c ℓ)` with `c` extended-valued; `Z`
nonempty. `E`, `F` are finite-dimensional real inner product spaces (the paper's `ℝ^{dx}`,
`ℝ^{dz}`), `I`, `L` finite types, possibly empty. Values are in `EReal`; feasible regions exclude
the bad objective value and "solvable" includes the infeasible case (p.40).
A strict Slater point of (D-B) is `StrictSlaterDB`: feasibility with `λ > 0`, strict and
relatively interior `zi ∈ Z`, and `(w0, z0)`, `(wi/λi, zi)` in the relative interiors of the
domains of the partial conjugates (a reading of Definition 2 for (D-B), implied by the literal
one; see `StrictSlaterDB`). Clause (ii) keeps the paper's one direction (p.13: the converse
fails). -/
theorem proposition_5 {E F ι L : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [Fintype ι] [Fintype L]
    (c : L → F → EReal) (f₀ : E → F → ℝ) (f : ι → E → F → ℝ)
    (hf₀ : IsRF f₀) (hf : ∀ i, IsRF (f i))
    (hc : ∀ ℓ, TensorAHPE.IsProperClosedConvex (c ℓ)) (hZ : (Z c).Nonempty) :
    dbVal c f₀ f ≤ dbpVal c f₀ f ∧
    ((∃ pS, StrictSlaterDB c f₀ f pS) →
      dbVal c f₀ f = dbpVal c f₀ f ∧
        (SolvableMax (dbFeas c f₀ f) (dbObj f₀ f) →
          SolvableMax (dbpFeas c f₀ f) (dbpObj f₀ f))) ∧
    (Bornology.IsBounded (Z c) →
      dbVal c f₀ f = dbpVal c f₀ f ∧
        (SolvableMax (dbpFeas c f₀ f) (dbpObj f₀ f) ↔
          SolvableMax (dbFeas c f₀ f) (dbObj f₀ f))) := by sorry

end PWDB
