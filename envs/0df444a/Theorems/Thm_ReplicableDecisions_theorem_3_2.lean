-- Prove2me | Theorems.Thm_ReplicableDecisions_theorem_3_2
-- name    : ReplicableDecisions.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:05:27.025231+00:00
-- url     : https://prove2.me/theorems/aa28120b-a379-4ac6-87db-17e861403b65
-- title:
--   Theorem 3.2 (values; the running-time sentence is not formalized) — exact binary profiles
-- statement:
--   Let $\mathcal Y=\{0,1\}$, let $G$ be any graph on the models, and let $D=\mathrm{dist}_G(A_0,A_1)$.
--
--   1. If $D<\infty$ and $k=\lceil D/2\rceil$, then $\Phi(G)=\dfrac1{k+1}$ and $\Psi(G)=\dfrac1k$.
--   2. If $3\le D<\infty$, then $\Lambda(G)=\dfrac1{k-1}$.
--   3. If $D\le2$, no neighborhood-correct selector exists.
--   4. If $D=\infty$, all three profiles are zero.
--
--   In each case the value is an attained minimum. The theorem solves the selector programs of the mission exactly, in terms of one integer.
--
--   **Formalization Note** Forced classes may be empty, in which case $D=\infty$.
--
--   Differences from the source:
--   - reading: the last sentence: the values and an implicit sampler can be constructed in O(M + |E|) time → not stated; reason: the paper fixes no machine model for this sentence (§2, p.9) and the goal does not use it; a cost model would be ours rather than the authors. Every value clause is stated in full
--   - encoding: a graph G = (P, E) → `SimpleGraph ι`, with `D` read through `forcedDist` in `ℕ∞`; reason: Mathlib graph and extended distance; the same object
--   - encoding: Y = {0, 1} → `Bool`, with 0 = `false` and 1 = `true`; reason: same two outputs
--   - encoding: the profile as a minimum over selector laws → `IsLeast` of the set of objective values at laws in `stdSimplex ℝ (ι → Y)`, with `DecidableEq ι` for the finite function type; reason: the page says all finite minima are attained; no instance changes
-- source:
--   Chen, Replicable Decisions in Finite Experiments, STOC 2027 submission (sha256 52d181db…), Theorem 3.2, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_ReplicableDecisions_forcedDist
import Definitions.Def_ReplicableDecisions_profileValues

namespace ReplicableDecisions

/-- **Theorem 3.2 (Exact binary profiles), the value clauses.** Chen, *Replicable Decisions in Finite
Experiments*, STOC 2027 submission (sha256 52d181db…), Theorem 3.2, p.11 (PDF p.13). Let
`D = dist_G(A₀, A₁)`. If `D < ∞` and `k = ⌈D/2⌉`, then `Φ(G) = 1/(k + 1)` and `Ψ(G) = 1/k`. If
`3 ≤ D < ∞`, then `Λ(G) = 1/(k − 1)`; if `D ≤ 2`, no neighborhood-correct selector exists. If `D = ∞`,
all three profiles are zero.

**Formalization Note.** `G` is an arbitrary graph on the models, and forced classes may be empty (then
`D = ∞`). Each value is `IsLeast` of the program's value set, so attainment is part of the statement.
`k − 1` is a real subtraction. The last sentence of the theorem, the `O(M + |E|)` construction time, is
not formalized: the paper fixes no machine model for it. -/
theorem theorem_3_2 {ι : Type*} [Fintype ι] [DecidableEq ι] (G : SimpleGraph ι)
    (Γ : ι → Set Bool) (hΓ : ∀ i, (Γ i).Nonempty) :
    (∀ D : ℕ, forcedDist G Γ false true = D →
      IsLeast (phiValues G Γ) (1 / ((⌈(D : ℝ) / 2⌉₊ : ℝ) + 1)) ∧
        IsLeast (psiValues G Γ) (1 / (⌈(D : ℝ) / 2⌉₊ : ℝ)) ∧
        (3 ≤ D → IsLeast (lambdaValues G Γ) (1 / ((⌈(D : ℝ) / 2⌉₊ : ℝ) - 1))) ∧
        (D ≤ 2 → ¬ ∃ f : ι → Bool, NeighborhoodCorrect G Γ f)) ∧
      (forcedDist G Γ false true = ⊤ →
        IsLeast (phiValues G Γ) 0 ∧ IsLeast (psiValues G Γ) 0 ∧ IsLeast (lambdaValues G Γ) 0) := by sorry

end ReplicableDecisions
