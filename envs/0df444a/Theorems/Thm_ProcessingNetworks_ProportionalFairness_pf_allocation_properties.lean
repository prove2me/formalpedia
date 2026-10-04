-- Prove2me | Theorems.Thm_ProcessingNetworks_ProportionalFairness_pf_allocation_properties
-- name    : ProcessingNetworks.ProportionalFairness.pf_allocation_properties
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-27T19:17:13.469342+00:00
-- url     : https://prove2.me/theorems/e6ede016-783f-49d8-aadc-1cc6a9a7f37d
-- title:
--   Lemma 10.1 — six properties of the PF allocation function ψ (milestone)
-- statement:
--   **Lemma 10.1.** Let $\mathcal I_+(z) := \{i : z_i > 0\}$. (a) $\psi(z)$ exists, and for $i \in
--   \mathcal I_+(z)$, $\psi_i(z)$ is uniquely determined and strictly positive. (b) If $\mathcal
--   I_+(z) \ne \emptyset$, $\psi(z)$ is extreme: every $x \in \mathcal A$ has some $i \in \mathcal
--   I_+(z)$ with $x_i \le \psi_i(z)$. (c) $\psi_i(rz) = \psi_i(z)$ for $r > 0$, $i \in \mathcal
--   I_+(z)$. (d) $\psi_i(\cdot)$ is continuous at $z$ for $i \in \mathcal I_+(z)$. (e) If $z \ne
--   0$, every interior point of $\mathcal A$ is strictly beaten by $\psi(z)$. (f) $z \mapsto
--   \max_{x\in\mathcal A} f(z,x)$ is continuous on $\mathbb R^I_+$.
--
--   This is the foundational existence/uniqueness/regularity package the rest of the chapter
--   builds on: without it, "$\psi$" would not even be a well-defined function.
--
--   **Formalization note.** All six parts are bundled into one theorem, matching the book's single
--   lettered lemma. Parts (e)/(f), stated in the book via `max_{x∈A} f(z,x)`, are restated via
--   `f z (psi AllocSet z)` directly (already established to equal the maximum by part (a)/the
--   definition of `IsPFMaximizer`), avoiding any separate `sSup`/`⨆` expression. The continuity
--   statements (d) and (f) are continuity *within* $\mathbb{R}^I_+$ (`ContinuousWithinAt` on the
--   orthant), which is the domain of $\psi$ and of $z \mapsto \max f(z, \cdot)$ ("continuous in $z$
--   on $\mathbb{R}^I_+$"): for a $z$ on the boundary of the orthant, nearby vectors with a negative
--   coordinate are outside the domain, and there `f` and `ψ` are junk (a negative weight on
--   $\log 0 = -\infty$), so unrestricted continuity at such $z$ would be false.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 184, Lemma 10.1

import Mathlib
import Definitions.Def_ProcessingNetworks_ProportionalFairness_PFOptimization

namespace ProcessingNetworks.ProportionalFairness

/-- Lemma 10.1, Dai & Harrison p. 184 (PDF p. 200): given `IsPFDomain AllocSet` and a demand
vector `z ≥ 0`, all six stated properties of the PF allocation function `ψ` hold. (a) existence is
built into `psi`'s definition; uniqueness and strict positivity hold on `I+(z) = {i : z_i > 0}`.
(b) extremality: if some class has positive demand, every feasible `x` is dominated by `ψ(z)` in
some such class. (c) scale invariance on `I+(z)`. (d) continuity of `ψ_i(·)` at `z`, for
`i ∈ I+(z)`. (e) `ψ(z)` strictly beats every interior point when `z ≠ 0`. (f) the optimal value
`f(·, ψ(·))` is continuous at `z`. -/
theorem pf_allocation_properties
    {I : ℕ} (AllocSet : Set (Fin I → ℝ)) (hdom : IsPFDomain AllocSet)
    (z : Fin I → ℝ) (hz : ∀ i, 0 ≤ z i) :
    IsPFMaximizer AllocSet z (psi AllocSet z) ∧
    (∀ i, 0 < z i →
      0 < psi AllocSet z i ∧ ∀ x, IsPFMaximizer AllocSet z x → x i = psi AllocSet z i) ∧
    ((∃ i, 0 < z i) → ∀ x ∈ AllocSet, ∃ i, 0 < z i ∧ x i ≤ psi AllocSet z i) ∧
    (∀ r : ℝ, 0 < r → ∀ i, 0 < z i → psi AllocSet (fun i => r * z i) i = psi AllocSet z i) ∧
    (∀ i, 0 < z i →
      ContinuousWithinAt (fun w => psi AllocSet w i) {w : Fin I → ℝ | ∀ i, 0 ≤ w i} z) ∧
    (z ≠ 0 → ∀ x ∈ interior AllocSet, f z x < f z (psi AllocSet z)) ∧
    ContinuousWithinAt (fun w => f w (psi AllocSet w)) {w : Fin I → ℝ | ∀ i, 0 ≤ w i} z := by sorry

end ProcessingNetworks.ProportionalFairness
