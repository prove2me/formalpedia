-- Prove2me | Theorems.Thm_ProcessingNetworks_ProportionalFairness_pf_aggregation_property
-- name    : ProcessingNetworks.ProportionalFairness.pf_aggregation_property
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-27T19:19:00.956819+00:00
-- url     : https://prove2.me/theorems/fb9750ea-29d4-477c-b8d3-815d8e2d54cf
-- title:
--   Proposition 10.2 — the aggregation property of ψ (milestone)
-- statement:
--   **Proposition 10.2.** With $y := Gz$ (i.e. $y_\ell = \sum_{i\in\mathcal I(\ell)} z_i$), the PF
--   allocation aggregates and splits: $\psi_i(z) = \tilde\psi_\ell(y)\cdot z_i/y_\ell$ for $i \in
--   \mathcal I(\ell)$, with $0/0 := 0$.
--
--   This is the "resource-relevant aggregation" property: implementing PF allocation only
--   requires knowing group-level aggregate demand, not individual class demands — crucial for
--   Section 12.6's multi-hop packet-network application.
--
--   **Formalization note.** `AllocSet`'s special structure (10.21) is a hypothesis
--   (`hAllocSet`) rather than baked into a shared record, since this proposition is stated
--   generically over any `AllocSet`/`TildeAllocSet` pair satisfying it; $\tilde{\mathcal A}$ has
--   the properties assumed of the allocation set in Section 10.1 (`hdom`), as Section 10.3
--   stipulates. Real division's built-in `x/0=0` convention in Lean matches the book's stated
--   `0/0:=0` exactly, needing no special case.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 192, Proposition 10.2

import Mathlib
import Definitions.Def_ProcessingNetworks_ProportionalFairness_PFOptimization
import Definitions.Def_ProcessingNetworks_ProportionalFairness_Aggregation

namespace ProcessingNetworks.ProportionalFairness

/-- Proposition 10.2, Dai & Harrison p. 192 (PDF p. 208): given `AllocSet = {x ≥ 0 : Gx ∈
TildeAllocSet}` (Eq. 10.21) for the demand-group assignment `grp` encoding `G`, and `y := Gz`
(Eq. 10.22, here `groupAggregate grp z`), the PF allocation splits as `ψ_i(z) = ψ̃_ℓ(y) · z_i/y_ℓ`
for each `i` in group `ℓ` (Eq. 10.24) — real division supplies the stated convention `0/0 = 0`
automatically. `Ã ⊂ ℝ^L_+` has the properties assumed of the allocation set in Section 10.1
(Section 10.3: "a set `Ã` that has all the properties assumed earlier for `A`"). -/
theorem pf_aggregation_property
    {I L : ℕ} (AllocSet : Set (Fin I → ℝ)) (TildeAllocSet : Set (Fin L → ℝ))
    (grp : Fin I → Fin L) (hdom : IsPFDomain TildeAllocSet)
    (hAllocSet : ∀ x : Fin I → ℝ,
      x ∈ AllocSet ↔ (∀ i, 0 ≤ x i) ∧ groupAggregate grp x ∈ TildeAllocSet)
    (z : Fin I → ℝ) (hz : ∀ i, 0 ≤ z i) (i : Fin I) :
    psi AllocSet z i =
      psi TildeAllocSet (groupAggregate grp z) (grp i) * z i / groupAggregate grp z (grp i) := by sorry

end ProcessingNetworks.ProportionalFairness
