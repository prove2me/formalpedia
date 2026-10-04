-- Prove2me | Theorems.Thm_TeschlQM_Dynamics_compactOperators_closed_star_ideal
-- name    : TeschlQM.Dynamics.compactOperators_closed_star_ideal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T06:59:45.927072+00:00
-- url     : https://prove2.me/theorems/30d1ca58-52a1-469b-aac3-040c0a7acabe
-- title:
--   Lemma 5.5 — the compact operators ℭ(ℌ) form a closed ∗-ideal in 𝔏(ℌ)
-- statement:
--   Let $\mathfrak C(\mathfrak H)$ be the norm closure in $\mathfrak L(\mathfrak H)$ of the finite rank operators. Then $\mathfrak C(\mathfrak H)$ is a closed $*$-ideal in $\mathfrak L(\mathfrak H)$: it is closed in the operator norm; it contains $0$ and is closed under sums and scalar multiples; for $K \in \mathfrak C(\mathfrak H)$ and $B \in \mathfrak L(\mathfrak H)$,
--   $$BK \in \mathfrak C(\mathfrak H), \qquad KB \in \mathfrak C(\mathfrak H);$$
--   and $K \in \mathfrak C(\mathfrak H)$ implies $K^* \in \mathfrak C(\mathfrak H)$.
--
--   **Formalization Note.** The adjoint is `star` on `H →L[ℂ] H`; products are compositions.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 128, Lemma 5.5

import Mathlib
import Definitions.Def_TeschlQM_Shared_compactOperators

namespace TeschlQM.Dynamics

/-- Teschl, Lemma 5.5, p. 128: the set `ℭ(ℌ)` of compact operators (the norm closure of the
finite rank operators) is a closed `∗`-ideal in `𝔏(ℌ)`: it is closed, it is a two-sided ideal
(contains `0`, is closed under sums and scalar multiples, and under multiplication by arbitrary
bounded operators on either side), and it is closed under taking adjoints (`star K = K*`). -/
theorem compactOperators_closed_star_ideal {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] :
    IsClosed (TeschlQM.Shared.compactOperators H) ∧ (0 : H →L[ℂ] H) ∈ TeschlQM.Shared.compactOperators H ∧
    (∀ K ∈ TeschlQM.Shared.compactOperators H, ∀ L ∈ TeschlQM.Shared.compactOperators H, K + L ∈ TeschlQM.Shared.compactOperators H) ∧
    (∀ (c : ℂ), ∀ K ∈ TeschlQM.Shared.compactOperators H, c • K ∈ TeschlQM.Shared.compactOperators H) ∧
    (∀ K ∈ TeschlQM.Shared.compactOperators H, ∀ B : H →L[ℂ] H,
      B * K ∈ TeschlQM.Shared.compactOperators H ∧ K * B ∈ TeschlQM.Shared.compactOperators H) ∧
    (∀ K ∈ TeschlQM.Shared.compactOperators H, star K ∈ TeschlQM.Shared.compactOperators H) := by sorry

end TeschlQM.Dynamics
