-- Prove2me | Theorems.Thm_ProcessingNetworks_ProportionalFairness_standard_load_condition_iff_gamma_lt_a
-- name    : ProcessingNetworks.ProportionalFairness.standard_load_condition_iff_gamma_lt_a
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-27T19:22:20.055315+00:00
-- url     : https://prove2.me/theorems/f45521cc-ae35-4079-a03f-8b890aa65d8d
-- title:
--   Proposition 10.4 — the standard load condition via γ < a (milestone)
-- statement:
--   **Proposition 10.4.** The standard load condition $\rho < b$ (equivalently, subcriticality,
--   Proposition 5.1) holds iff $\gamma < a$ for some $a \in \tilde{\mathcal A}$ (Eq. 10.37), where
--   $\gamma_\ell := \sum_{i\in\mathcal I(\ell)} \alpha_i m_i$ (Eq. 10.36) is the aggregate service
--   effort demanded per unit time by group $\ell$.
--
--   This restates subcriticality in the reduced, group-level coordinates that Theorem 10.5's proof
--   actually uses, rather than the original $K$-dimensional capacity coordinates.
--
--   **Formalization note.** The book's own proof is "left as an exercise"; the statement is
--   formalized as a genuine `↔`, neither direction dropped. The reduced allocation set is tied to
--   the network's capacity data as in Section 10.4: the demand groups are the classes with identical
--   columns of $A$ (`hgrp`), $\tilde A$ is the $K \times L$ matrix of the groups' common columns
--   (`hAtil`), and $\tilde{\mathcal A} = \{y \in \mathbb{R}^L_+ : \tilde A y \le b\}$ (10.27,
--   `hTilde`) — without this relation between $\tilde{\mathcal A}$ and $(A, b)$ the equivalence
--   would have no content; $A \ge 0$, $b > 0$ and $\alpha \ge 0$ as for every unitary network.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 196, Proposition 10.4, Eqs. (10.36),(10.37)

import Mathlib
import Definitions.Def_ProcessingNetworks_ProportionalFairness_FluidModel
import Definitions.Def_ProcessingNetworks_ProportionalFairness_Aggregation

namespace ProcessingNetworks.ProportionalFairness

/-- The standard load condition `ρ < b` (Eq. 5.1, restated from mission II) for a unitary network
with capacity consumption matrix `Amat` and capacities `bvec`: `A(α ⊙ m) < b` componentwise. -/
def StandardLoadCondition {I K : ℕ} (Amat : Matrix (Fin K) (Fin I) ℝ) (bvec : Fin K → ℝ)
    (alpha m : Fin I → ℝ) : Prop :=
  ∀ k, (Amat.mulVec (fun i => alpha i * m i)) k < bvec k

/-- Proposition 10.4, Dai & Harrison p. 196 (PDF p. 212): the standard load condition (5.1) holds
for a unitary network (equivalently, the network is subcritical) if and only if `γ < a` for some
`a ∈ Ã` (Eq. 10.37), where `γ_ℓ := ∑_{i ∈ I(ℓ)} α_i m_i` (Eq. 10.36, here
`groupAggregate dat.grp (fun i => alpha i * dat.m i)`). The demand groups are the classes with
identical columns of the capacity consumption matrix `A` (Section 10.4), `Ã` is the `K × L`
matrix of the groups' common columns, and `Ã = {y ∈ ℝ^L_+ : Ãy ≤ b}` (10.27) — without this
relation between the reduced allocation set and `(A, b)` the equivalence has no content. The
book's own proof is "left as an exercise." -/
theorem standard_load_condition_iff_gamma_lt_a
    {I L K : ℕ} (dat : PFUnitaryNetworkData I L)
    (Amat : Matrix (Fin K) (Fin I) ℝ) (bvec : Fin K → ℝ) (Atil : Matrix (Fin K) (Fin L) ℝ)
    (hA : ∀ k i, 0 ≤ Amat k i) (hb : ∀ k, 0 < bvec k)
    (hgrp : ∀ i j, dat.grp i = dat.grp j ↔ ∀ k, Amat k i = Amat k j)
    (hAtil : ∀ k i, Atil k (dat.grp i) = Amat k i)
    (hTilde : dat.TildeAllocSet = {y | (∀ ℓ, 0 ≤ y ℓ) ∧ ∀ k, (Atil.mulVec y) k ≤ bvec k})
    (alpha : Fin I → ℝ) (halpha : IsTotalArrivalRates dat alpha) (hα : ∀ i, 0 ≤ alpha i) :
    StandardLoadCondition Amat bvec alpha dat.m ↔
      ∃ a ∈ dat.TildeAllocSet, ∀ ℓ, groupAggregate dat.grp (fun i => alpha i * dat.m i) ℓ < a ℓ := by sorry

end ProcessingNetworks.ProportionalFairness
