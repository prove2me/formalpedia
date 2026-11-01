-- Prove2me | Theorems.Thm_PWDB_theorem_7
-- name    : PWDB.theorem_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:39:12.682335+00:00
-- url     : https://prove2.me/theorems/b5e7b0e1-5418-4674-8660-89c14330c042
-- title:
--   Theorem 7 — strong duality between the primal worst (P-W) and dual best (D-B) problems
-- statement:
--   Let $E, F$ be finite-dimensional real inner product spaces, $I$, $L$ finite index sets, $f_0, f_i : E \times F \to \mathbb R$ satisfy (RF) (convex in $x$, concave in $z$), and $c_\ell : F \to \overline{\mathbb R}$ satisfy (C) (proper, closed, convex), with $Z = \{z \mid c_\ell(z) \le 0\ \forall \ell\}$ nonempty.
--
--   1. If (P-W) admits a strict Slater point and $Z$ is bounded, then $\inf(\mathrm{P\text{-}W}) = \sup(\mathrm{D\text{-}B})$ and (D-B) is solvable.
--   2. If the feasible region of (P-W) is nonempty and bounded and $Z$ is bounded, then $\inf(\mathrm{P\text{-}W}) = \sup(\mathrm{D\text{-}B})$ and (P-W) is solvable.
--   3. If (D-B) admits a strict Slater point, then $\sup(\mathrm{D\text{-}B}) = \inf(\mathrm{P\text{-}W})$ and (P-W) is solvable.
--
--   Here (P-W) is $\inf_x \sup_{z_0\in Z} f_0(x,z_0)$ s.t. $\sup_{z_i \in Z} f_i(x,z_i) \le 0$, and (D-B) is $\sup -f_0^{*1}(w_0,z_0) - \sum_i \lambda_i f_i^{*1}(w_i/\lambda_i, z_i)$ s.t. $\sum_{i\in I_0} w_i = 0$, $z_i \in Z$, $\lambda \ge 0$. This is the primal-worst-equals-dual-best principle: the robust counterpart equals the optimistic dual. Clause (iii) does not require $Z$ to be bounded.
--
--   Differences from the source:
--   - generalization: ℝ^{dx}, ℝ^{dz} → finite-dimensional real inner product spaces E, F; reason: every ℝ^d with the dot product is such a space, so the Lean statement specializes to the printed one
--   - encoding: (RF): fi(·, z) proper closed convex, −fi(x, ·) proper closed convex → fi : E → F → ℝ real-valued with IsRF (convex in x, concave in z); reason: p.8 proves (RF) forces real values; a real-valued convex function on a finite-dimensional space is continuous, hence proper and closed; same instances
--   - encoding: (C): cℓ proper, closed and convex, Z nonempty → TensorAHPE.IsProperClosedConvex (c ℓ) with c extended-valued, hypothesis (Z c).Nonempty; reason: standing assumptions of p.9, stated as binders; same instances
--   - encoding: index sets I, L, I0 = {0} ∪ I, L0 = {0} ∪ L → Fintype ι, L (possibly empty), Option ι, Option L with none as the index 0; reason: Lean convention; same instances
--   - encoding: optimal values, feasible regions and solvability of p.40 → EReal ⨅/⨆ over the feasible region; feasibility excludes the bad objective value; Solvable includes the infeasible case; reason: Lean transcription of the conventions stated on p.40; same instances
--   - encoding: convex perspective on ℝ^{dx} × ℝ₊ (Definitions A.2, A.4) → persp/pPersp with value +∞ for t < 0; reason: every multiplier in the paper is ≥ 0; no value at t ≥ 0 changes
--   - generalization: strict Slater point of (D-B) (Definition 2: point in ri(dom(−objective)) in the variables (w, z, λ)) → StrictSlaterDB: feasible, λ > 0, cℓ(zi) < 0 and zi ∈ ri dom cℓ, (w0, z0) ∈ ri dom f0∗1, (wi/λi, zi) ∈ ri dom fi∗1; reason: the literal condition implies StrictSlaterDB (the slice of dom(−objective) at fixed λi > 0 is the image of dom fi∗1 under (w, z) ↦ (λi w, z)); the literal ri can be empty (f0 = x, f1 = zx − 1, Z = ℝ), which would make the clause vacuous; StrictSlaterDB is what the proof on p.55 uses
-- source:
--   Zhen, Kuhn & Wiesemann, A Unified Theory of Robust and Distributionally Robust Optimization via the Primal-Worst-Equals-Dual-Best Principle, arXiv:2105.00760v2 (19 Jul 2023), Theorem 7, p.13 (proof pp.53–55)

import Mathlib
import Definitions.Def_TensorAHPE_IsProperClosedConvex
import Definitions.Def_PWDB_IsRF
import Definitions.Def_PWDB_RobustProgram
import Definitions.Def_PWDB_Slater
import Definitions.Def_PWDB_StrictSlaterDB
import Definitions.Def_PWDB_Solvable

namespace PWDB

/-- **Theorem 7 (Strong Duality for (P-W) and (D-B))** (Zhen, Kuhn & Wiesemann,
arXiv:2105.00760v2, Theorem 7, p.13): "The following statements hold.
(i) If (P-W) admits a strict Slater point and Z is bounded, then the infimum of (P-W) coincides
with the supremum of (D-B), and (D-B) is solvable.
(ii) If the feasible region of (P-W) is nonempty and bounded and Z is bounded, then the infimum of
(P-W) coincides with the supremum of (D-B), and (P-W) is solvable.
(iii) If (D-B) admits a strict Slater point, then its supremum coincides with the infimum of
(P-W), and (P-W) is solvable."

**Formalization Note** Standing assumptions of §3 (pp.8–9) are binders: (RF) as `IsRF` for real-valued `f0`, `fi`
(p.8 shows (RF) forces real values; on finite-dimensional spaces real-valued convex–concave is
exactly (RF)); (C) as `TensorAHPE.IsProperClosedConvex (c ℓ)` with `c` extended-valued; `Z`
nonempty. `E`, `F` are finite-dimensional real inner product spaces (the paper's `ℝ^{dx}`,
`ℝ^{dz}`), `I`, `L` finite types, possibly empty. Values are in `EReal`; feasible regions exclude
the bad objective value and "solvable" includes the infeasible case (p.40).
A strict Slater point of (P-W) is `StrictSlaterMin` (Definition 2) for the objective
`sup_{z∈Z} f0(x, z)` and the constraints `sup_{z∈Z} fi(x, z) ≤ 0`, with no equality constraints.
A strict Slater point of (D-B) is `StrictSlaterDB` (a reading of Definition 2 for (D-B), implied by
the literal one; see its docstring). Clause (iii) has no boundedness assumption on `Z`. -/
theorem theorem_7 {E F ι L : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [Fintype ι] [Fintype L]
    (c : L → F → EReal) (f₀ : E → F → ℝ) (f : ι → E → F → ℝ)
    (hf₀ : IsRF f₀) (hf : ∀ i, IsRF (f i))
    (hc : ∀ ℓ, TensorAHPE.IsProperClosedConvex (c ℓ)) (hZ : (Z c).Nonempty) :
    ((∃ xS, StrictSlaterMin (worst c f₀) (fun i => worst c (f i)) (fun e : Empty => e.elim) xS) →
      Bornology.IsBounded (Z c) →
      pwVal c f₀ f = dbVal c f₀ f ∧ SolvableMax (dbFeas c f₀ f) (dbObj f₀ f)) ∧
    ((pwFeas c f₀ f).Nonempty → Bornology.IsBounded (pwFeas c f₀ f) →
      Bornology.IsBounded (Z c) →
      pwVal c f₀ f = dbVal c f₀ f ∧ SolvableMin (pwFeas c f₀ f) (worst c f₀)) ∧
    ((∃ pS, StrictSlaterDB c f₀ f pS) →
      dbVal c f₀ f = pwVal c f₀ f ∧ SolvableMin (pwFeas c f₀ f) (worst c f₀)) := by sorry

end PWDB
