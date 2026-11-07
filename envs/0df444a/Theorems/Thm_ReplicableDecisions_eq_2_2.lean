-- Prove2me | Theorems.Thm_ReplicableDecisions_eq_2_2
-- name    : ReplicableDecisions.eq_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:04:31.09758+00:00
-- url     : https://prove2.me/theorems/5de62844-52cb-4a5b-a92f-9fe136ddda75
-- title:
--   Equation (2.2) — $\mathrm{TV}(P^n,Q^n)\le\sqrt{2(1-(1-h^2(P,Q))^n)}\le\sqrt{2n}\,h(P,Q)$
-- statement:
--   Let $P,Q$ be probability vectors on a finite set $\mathcal Z$ and let $n\ge0$. Then
--
--   $$
--   \mathrm{TV}(P^n,Q^n)\le\sqrt{2\bigl(1-(1-h^2(P,Q))^n\bigr)}\le\sqrt{2n}\,h(P,Q).
--   $$
--
--   This is how a Hellinger step between models becomes a bound on how well $n$ samples distinguish them; it fixes the radius $1/\sqrt{32n}$ of the lower bound.
--
--   Differences from the source:
--   - encoding: a finite set Z → `Z : Type` with `Fintype Z`; reason: the reused Bhattacharyya coefficient takes a type in `Type`; no finite Z is lost
-- source:
--   Chen, Replicable Decisions in Finite Experiments, STOC 2027 submission (sha256 52d181db…), equation (2.2), p.9 (PDF p.11)

import Mathlib
import Definitions.Def_ReplicableDecisions_hellinger
import Definitions.Def_ReplicableDecisions_Experiment

namespace ReplicableDecisions

/-- **The tensorized TV–Hellinger bound, (2.2).** Chen, *Replicable Decisions in Finite Experiments*,
STOC 2027 submission (sha256 52d181db…), equation (2.2), p.9 (PDF p.11):
`TV(Pⁿ, Qⁿ) ≤ √(2(1 − (1 − h²(P, Q))ⁿ)) ≤ √(2n) h(P, Q)`, for all probability vectors and every `n`. -/
theorem eq_2_2 {Z : Type} [Fintype Z] {P Q : Z → ℝ} (hP : P ∈ stdSimplex ℝ Z)
    (hQ : Q ∈ stdSimplex ℝ Z) (n : ℕ) :
    tv (productLaw P (n := n)) (productLaw Q (n := n)) ≤
        Real.sqrt (2 * (1 - (1 - hellingerSq P Q) ^ n)) ∧
      Real.sqrt (2 * (1 - (1 - hellingerSq P Q) ^ n)) ≤ Real.sqrt (2 * n) * hellinger P Q := by sorry

end ReplicableDecisions
