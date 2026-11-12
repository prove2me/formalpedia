-- Prove2me | Theorems.Thm_RiskAverseConsistency_proposition_9
-- name    : RiskAverseConsistency.proposition_9
-- status  : Proved
-- author  : @iris
-- created : 2026-11-03T05:22:23.309591+00:00
-- url     : https://prove2.me/theorems/cd38b8df-2894-4d75-9bad-d00137e8428b
-- title:
--   Proposition 9 — epiconvergence plus complete continuity gives Mosco-epiconvergence
-- statement:
--   Let $Z_0\subset Z$ be a nonempty, closed, convex subset of a reflexive Banach space $Z$ and $Y_0\subset Y$ a closed subset of a Banach space $Y$. Suppose $\mathbf B:Z\to Y$ is linear and completely continuous with $\mathbf B(Z_0)\subset Y_0$. If $h_k:Y_0\to(-\infty,\infty]$ epiconverges to $h:Y_0\to(-\infty,\infty]$ and $h_k\circ\mathbf B:Z_0\to(-\infty,\infty]$ epiconverges to $h\circ\mathbf B$, then
--
--   $$
--   h_k\circ\mathbf B\ \text{ Mosco-epiconverges to }\ h\circ\mathbf B\ \text{ on } Z_0 .
--   $$
--
--   This is how norm-topology epiconvergence results (such as the epigraphical law of large numbers) are transferred to the weak topology needed in infinite dimensional decision spaces, as in PDE-constrained problems where $\mathbf B$ is the adjoint of a compact embedding.
--
--   Differences from the source:
--   - encoding: functions with values in (−∞, ∞] → EReal-valued functions with the value ⊥ = −∞ excluded on the domain set; reason: Lean convention; same instances
--   - encoding: functions defined on the subset (V₀, Z_ad, Y₀) → functions on the ambient space whose values off the subset are never used; reason: Lean convention; every quantifier is restricted to the subset, so no instance changes
--   - encoding: B : Z → Y linear and completely continuous → B : Z →ₗ[ℝ] Y with CompletelyContinuousOn univ B; reason: same instances; no boundedness is added
-- source:
--   Milz, Surowiec, Asymptotic consistency for nonconvex risk-averse stochastic optimization with infinite dimensional decision spaces, arXiv:2207.14756v2, p.8, Proposition 9 (complete continuity defined on p.8)

import Mathlib
import Definitions.Def_QuasiHemiVI_Existence_WeakConv
import Definitions.Def_RiskAverseConsistency_EpiConvergesOn
import Definitions.Def_RiskAverseConsistency_MoscoConvergesOn
import Definitions.Def_RiskAverseConsistency_CompletelyContinuousOn

open Filter Topology QuasiHemiVI.Existence

namespace RiskAverseConsistency

/-- **Proposition 9.** Let `Z₀ ⊂ Z` be a nonempty, closed, convex subset of a reflexive Banach space
`Z` and `Y₀ ⊂ Y` a closed subset of a Banach space `Y`. Suppose `B : Z → Y` is linear and completely
continuous with `B(Z₀) ⊂ Y₀`. If `hₖ : Y₀ → (−∞, ∞]` epiconverges to `h : Y₀ → (−∞, ∞]` and
`hₖ ∘ B : Z₀ → (−∞, ∞]` epiconverges to `h ∘ B`, then `hₖ ∘ B` Mosco-epiconverges to `h ∘ B` on `Z₀`.

Milz, Surowiec, arXiv:2207.14756v2, Proposition 9, p.8.

Formalization Note: `(−∞, ∞]`-valued functions are `EReal`-valued with `⊥` excluded on `Y₀`.
Epiconvergence on the complete metric spaces `Y₀` and `Z₀` (closed subsets of Banach spaces) is
`EpiConvergesOn Y₀` and `EpiConvergesOn Z₀`. -/
theorem proposition_9 {Z Y : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y] (hZ : IsReflexive Z)
    {Z₀ : Set Z} (hZ₀_ne : Z₀.Nonempty) (hZ₀_closed : IsClosed Z₀) (hZ₀_convex : Convex ℝ Z₀)
    {Y₀ : Set Y} (hY₀_closed : IsClosed Y₀) (B : Z →ₗ[ℝ] Y)
    (hB : CompletelyContinuousOn Set.univ B) (hBZ₀ : Set.MapsTo B Z₀ Y₀)
    (h : ℕ → Y → EReal) (hlim : Y → EReal) (h_ne_bot : ∀ k, ∀ y ∈ Y₀, h k y ≠ ⊥)
    (hlim_ne_bot : ∀ y ∈ Y₀, hlim y ≠ ⊥) (hepi : EpiConvergesOn Y₀ h hlim)
    (hepiB : EpiConvergesOn Z₀ (fun k z => h k (B z)) (fun z => hlim (B z))) :
    MoscoConvergesOn Z₀ (fun k z => h k (B z)) (fun z => hlim (B z)) := by sorry

end RiskAverseConsistency
