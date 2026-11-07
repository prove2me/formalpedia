-- Prove2me | Theorems.Thm_VecBalPoly_lemma_4_1
-- name    : VecBalPoly.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T23:14:42.045092+00:00
-- url     : https://prove2.me/theorems/6badc7b2-a947-403e-8b65-777888b30b7c
-- title:
--   Lemma 4.1 — fewer than $5s/K$ row constraints
-- statement:
--   At any state after cleanup with $s>K$ and $L\le2$, the number of large rows plus the number of nearly tight pairs $(i,\sigma)$ — $i$ a medium row, $\sigma\in\{-1,1\}$ and $u_{i\sigma}\ge-1$ — is less than
--   $$\frac{5s}{K}.$$
--
--   So the linear constraints imposed on an update remove only a small fraction of the $s$ degrees of freedom.
--
--   Differences from the source:
--   - generalization: a state after cleanup of Algorithm 2.2 → any state satisfying IsClean (cube, V = {|x_j| < 1}, T_i ⊆ V, (2.2), (2.3) on medium rows, column norms ≤ 1); reason: every post-cleanup state of a run satisfies these conditions, and the proof uses only them
--   - generalization: m ≥ 1 (the standing assumption of Theorem 1.1) → m = 0 also allowed; reason: with no rows there are no row constraints and the row sums are empty; the source's cases m ≥ 1 are included unchanged
--   - encoding: row, column and sign indices i ∈ [m], j ∈ [n], σ ∈ {−1, 1} → Fin m, Fin n (0-based) and σ : Bool with sgn true = 1, sgn false = −1; reason: Lean conventions; same instances
-- source:
--   S. Guo, E. X. Fang, J. Lu, Vector Balancing in Polynomial Time, arXiv:2609.23540 (held file sha256 b777ade4…), Lemma 4.1, p.8 (PDF p.9)

import Mathlib
import Definitions.Def_VecBalPoly_IsClean
import Definitions.Def_VecBalPoly_L

namespace VecBalPoly

open Classical

/-- **Lemma 4.1 (counting row constraints).**
Guo, Fang, Lu, *Vector Balancing in Polynomial Time*, arXiv:2609.23540 (held file sha256
b777ade4…), Lemma 4.1, p.8 (PDF p.9): "At any state after cleanup with s > K and L ≤ 2, the number of
large rows plus the number of nearly tight pairs (i, σ) is less than 5s/K."

**Formalization Note** "State after cleanup" is `IsClean`. Nearly tight pairs are pairs
`(i, σ)` of a medium row and a sign with `u_{iσ} ≥ −1` (barriers exist for medium rows only,
§2.2). -/
theorem lemma_4_1 :
    ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (st : St m n), IsClean A st →
      K < (st.V.card : ℝ) → L A st ≤ 2 →
      ((Finset.univ.filter (fun i => IsLarge A st i)).card +
        (Finset.univ.filter (fun iσ : Fin m × Bool =>
          IsMedium A st iσ.1 ∧ -1 ≤ u A st iσ.1 iσ.2)).card : ℝ) < 5 * st.V.card / K := by sorry

end VecBalPoly
