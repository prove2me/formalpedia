-- Prove2me | Theorems.Thm_PHarmGradientCompactness
-- name    : PHarmGradientCompactness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:25:14.236944+00:00
-- url     : https://prove2.me/theorems/a94d9d25-8ead-4543-9126-a8481b24bbd2
-- title:
--   PHarm Gradient Compactness: PHarm Gradient Compactness
-- statement:
--   Compactness of a locally uniformly bounded family of `p`-harmonic functions,
--   in the gradient.  Let `Ω` be an increasing sequence of domains, let `v n` be
--   `p`-harmonic on `Ω n`, and suppose the family is eventually uniformly bounded on
--   every compact subset of the union.  Then every `v n` is `C^1` on `Ω n`, and there is
--   a single subsequence along which both `v` and its classical gradient converge
--   uniformly on every compact subset of the union.
--
--   The domains are allowed to grow because the blow-ups `u_r` are `p`-harmonic only on
--   `ball 0 (ρ / r)`; a constant-domain statement would force a second diagonal
--   argument on the consumer.  Taking `Ω` constant recovers the fixed-ball form that the
--   compact family of the paper's high-order growth section needs, so one statement
--   serves both consumers.
--
--   The gradients carried here are the CLASSICAL ones.  Nothing is asserted relating the
--   limit `G` to the gradient of the limit `V`: that identification is exactly what is
--   not available, and it is not needed, because the rigidity input quantifies its weak
--   gradient existentially.
--
--   Source: https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/PHarmGradientCompactness.lean#L23-L138
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/PHarmGradientCompactness.lean#L23-L138

import Definitions.Def_PHigherOrder_PHarmJetEquicontinuity
import Definitions.Def_PHigherOrder_PHarmRestrict
import Definitions.Def_PHigherOrder_PHarmJetTailEstimate
import Definitions.Def_PHigherOrder_JetLocalCompactness
import Definitions.Def_PHigherOrder_PHarmGradientCompactness
import Theorems.Thm_JetLocalCompactness
import Theorems.Thm_PHarmJetEquicontinuity
import Theorems.Thm_PHarmJetTailEstimate
import Theorems.Thm_PHarmRestrict

set_option autoImplicit false

theorem PHarmGradientCompactness (p : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (F : FirstOrderEstimateInput p)
    (Ω : ℕ → Set Plane) (hmono : Monotone Ω)
    (v : ℕ → Plane → ℝ) (g : ℕ → Plane → Plane)
    (hph : ∀ n : ℕ, IsPHarm p (Ω n) (v n) (g n))
    (hbd : ∀ K : Set Plane, K ⊆ (⋃ n, Ω n) → IsCompact K →
        ∃ M : ℝ, 0 < M ∧ ∃ N : ℕ, ∀ n, N ≤ n → ∀ z ∈ K, |v n z| ≤ M) :
    (∀ n : ℕ, ContDiffOn ℝ 1 (v n) (Ω n)) ∧
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (V : Plane → ℝ) (G : Plane → Plane),
      (∀ K : Set Plane, K ⊆ (⋃ n, Ω n) → IsCompact K →
          TendstoUniformlyOn (fun i => v (φ i)) V Filter.atTop K) ∧
      (∀ K : Set Plane, K ⊆ (⋃ n, Ω n) → IsCompact K →
          TendstoUniformlyOn (fun i => gradient (v (φ i))) G Filter.atTop K) := by sorry
