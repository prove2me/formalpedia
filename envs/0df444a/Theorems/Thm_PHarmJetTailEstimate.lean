-- Prove2me | Theorems.Thm_PHarmJetTailEstimate
-- name    : PHarmJetTailEstimate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:22:02.136927+00:00
-- url     : https://prove2.me/theorems/d0483a0f-5725-4979-bed8-642f07e2ccd5
-- title:
--   PHarm Jet Tail Estimate: PHarm Jet Tail Estimate
-- statement:
--   The per-compact tail estimate feeding the Arzela-Ascoli step.  On a compact
--   `K` inside the union of an increasing family of domains, all but finitely many
--   members of a locally uniformly bounded family of `p`-harmonic functions are
--   simultaneously `C^1` near `K`, bounded there, Lipschitz there, and have gradients
--   bounded and uniformly Holder there, with constants independent of the index.
--
--   This is where the `p`-harmonicity is spent.  It converts the one-ball statement of
--   `PHarmJetEquicontinuity` into a statement about a whole tail of the family on an
--   arbitrary compact subset of the union:  the compact has to be thickened to buy room
--   for the doubled ball, the exhaustion has to be collapsed to a single domain index,
--   and the Holder bound on the gradient has to be supplemented by a Lipschitz bound on
--   the function itself, which the Holder bound does not give.  The estimates are stated
--   only for nearby pairs `‖z - z'‖ < 3 R / 4`, which is all a modulus of continuity
--   needs and all the one-ball estimate supplies.
--
--   Source: https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/PHarmJetTailEstimate.lean#L18-L124
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/PHarmJetTailEstimate.lean#L18-L124

import Definitions.Def_PHigherOrder_PHarmJetEquicontinuity
import Definitions.Def_PHigherOrder_PHarmRestrict
import Definitions.Def_PHigherOrder_PHarmJetTailEstimate
import Theorems.Thm_PHarmJetEquicontinuity
import Theorems.Thm_PHarmRestrict

set_option autoImplicit false

theorem PHarmJetTailEstimate (p : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (F : FirstOrderEstimateInput p)
    (Ω : ℕ → Set Plane) (hmono : Monotone Ω)
    (v : ℕ → Plane → ℝ) (g : ℕ → Plane → Plane)
    (hph : ∀ n : ℕ, IsPHarm p (Ω n) (v n) (g n))
    (hbd : ∀ K : Set Plane, K ⊆ (⋃ n, Ω n) → IsCompact K →
        ∃ M : ℝ, 0 < M ∧ ∃ N : ℕ, ∀ n, N ≤ n → ∀ z ∈ K, |v n z| ≤ M)
    (K : Set Plane) (hK : K ⊆ (⋃ n, Ω n)) (hKc : IsCompact K) :
    ∃ (N : ℕ) (A L R : ℝ), 0 < A ∧ 0 < L ∧ 0 < R ∧ ∀ n, N ≤ n →
      ContinuousOn (v n) K ∧ ContinuousOn (fun z => gradient (v n) z) K ∧
      (∀ z ∈ K, |v n z| ≤ A) ∧
      (∀ z ∈ K, ‖gradient (v n) z‖ ≤ L) ∧
      (∀ z ∈ K, ∀ z' ∈ K, ‖z - z'‖ < 3 * R / 4 →
        ‖gradient (v n) z - gradient (v n) z'‖ ≤ L * (‖z - z'‖ / (2 * R)) ^ F.kappa) ∧
      (∀ z ∈ K, ∀ z' ∈ K, ‖z - z'‖ < 3 * R / 4 → |v n z - v n z'| ≤ L * ‖z - z'‖) := by sorry
