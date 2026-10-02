-- Prove2me | Theorems.Thm_ProcessingNetworks_Subcriticality_unitary_network_subcritical_iff_standard_load_condition
-- name    : ProcessingNetworks.Subcriticality.unitary_network_subcritical_iff_standard_load_condition
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T17:28:05.25711+00:00
-- url     : https://prove2.me/theorems/867712ff-930b-4983-9bdf-2f59464e461a
-- title:
--   Proposition 5.1 — a unitary network is subcritical iff the standard load condition holds
-- statement:
--   A **unitary network** (Section 2.6) is a network with one activity per class, class-changing
--   governed by a substochastic, transient routing matrix $P$ ($P^n \to 0$ entrywise as $n \to
--   \infty$): $P_{ij}$ is the probability a completed class-$i$ service becomes a class-$j$ item.
--   Transience makes $I - P^\top$ invertible, giving a unique **throughput-rate vector** $\alpha$
--   solving
--   $$
--   (I - P^\top)\alpha = \lambda \qquad \text{(Eq. 2.38)},
--   $$
--   and a **load vector**
--   $$
--   \rho := A\,\operatorname{diag}(m)\,\alpha \qquad \text{(Eq. 2.40)},
--   $$
--   where $A$ is the capacity consumption matrix and $m$ the mean service times. The **standard
--   load condition** (5.1) is $\rho < b$ (strict, componentwise), where $b$ is the vector of server
--   capacities.
--
--   **Proposition 5.1.** A unitary network is subcritical (i.e. its static-planning-problem optimal
--   value satisfies $\gamma^\ast < 1$, for the specialization $R = (I-P^\top)M^{-1}$ that a unitary
--   network's material-balance data reduces to) if and only if the standard load condition $\rho <
--   b$ holds.
--
--   This is the book's bridge between the abstract LP-based subcriticality of Section 5.2 and the
--   concrete, easily checked load condition familiar from classical queueing theory (e.g. Jackson
--   network stability).
--
--   **Formalization note.** $\alpha$ is taken as an explicit hypothesis-supplied vector satisfying
--   its defining equation $(I-P^\top)\alpha = \lambda$, rather than as `(1 - Pᵀ)⁻¹λ` computed via a
--   general matrix inverse — transience already pins $\alpha$ uniquely given that equation, and this
--   avoids committing the statement to a particular matrix-inversion API. The arrival-rate vector
--   is nonnegative, $\lambda \in \mathbb{R}^I_+$, as throughout Chapter 5 (for a $\lambda$ with a
--   negative entry the SPP has no feasible $x \ge 0$ while $\rho < b$ can still hold, so the
--   equivalence is only claimed, and only true, on $\mathbb{R}^I_+$).
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 94, Proposition 5.1

import Mathlib
import Definitions.Def_ProcessingNetworks_Subcriticality_SPNPlanningData
import Definitions.Def_ProcessingNetworks_Subcriticality_StaticPlanningProblem

namespace ProcessingNetworks.Subcriticality

/-- Proposition 5.1, p. 94 (PDF p. 110): a unitary network is subcritical if and only if it
satisfies the standard load condition (5.1), `ρ < b`. `P` is the network's routing matrix,
substochastic (`hP_nonneg`, `hP_rowsum`) and transient (`hP_transient`, `Pⁿ → 0` entrywise, as in
Section 2.6); `α` is the throughput-rate vector solving `(1 - Pᵀ)α = λ` (Eq. (2.38)), and the load
vector is `ρ = A·diag(m)·α` (Eq. (2.40)), with `A`, `m`, `b` as usual; the arrival-rate vector
`λ ∈ ℝ^I_+` is nonnegative, as throughout (Section 5.3). -/
theorem unitary_network_subcritical_iff_standard_load_condition
    {I K : ℕ} (P : Matrix (Fin I) (Fin I) ℝ)
    (hP_nonneg : ∀ i j, 0 ≤ P i j) (hP_rowsum : ∀ i, ∑ j, P i j ≤ 1)
    (hP_transient : ∀ i j, Filter.Tendsto (fun n => (P ^ n) i j) Filter.atTop (nhds 0))
    (m : Fin I → ℝ) (hm : ∀ i, 0 < m i)
    (A : Matrix (Fin K) (Fin I) ℝ) (b : Fin K → ℝ) (hb : ∀ k, 0 < b k)
    (lam alpha : Fin I → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (halpha : (1 - P.transpose).mulVec alpha = lam) :
    lam ∈ SubcriticalRegion (SPNPlanningData.ofUnitary P m hm A b hb) ↔
      ∀ k, (A.mulVec ((Matrix.diagonal m).mulVec alpha)) k < b k := by sorry

end ProcessingNetworks.Subcriticality
