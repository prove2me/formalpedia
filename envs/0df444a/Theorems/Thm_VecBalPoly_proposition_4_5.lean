-- Prove2me | Theorems.Thm_VecBalPoly_proposition_4_5
-- name    : VecBalPoly.proposition_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T23:16:27.854189+00:00
-- url     : https://prove2.me/theorems/ed66b74c-c0de-48e8-97e7-0ae9119b564e
-- title:
--   Proposition 4.5 — existence of negative curvature
-- statement:
--   At any state after cleanup with $s>K$ and $L\le2$, for every $g_*\in\mathbb R^V$ there is a unit vector $h\in\mathbb R^V$ orthogonal to $g_*$, to the retained row vectors $b_i$ of all large rows, and to the gradients $g_{i\sigma}$ of all nearly tight barriers ($i$ medium, $u_{i\sigma}\ge-1$), such that
--   $$h^{\mathsf T}\nabla^2\Phi\,h\le-2\eta.$$
--
--   This is the main mathematical guarantee behind Lemma 2.1: the row constraints leave room for a direction along which the potential is strictly concave.
--
--   Differences from the source:
--   - generalization: a state after cleanup of Algorithm 2.2 → any state satisfying IsClean (cube, V = {|x_j| < 1}, T_i ⊆ V, (2.2), (2.3) on medium rows, column norms ≤ 1); reason: every post-cleanup state of a run satisfies these conditions, and the proof uses only them
--   - encoding: ∇Φ, ∇²Φ with V, T_i, c_i, r_i fixed (gradient in the active coordinates) → Fréchet derivatives (fderiv) of y ↦ Φ(y; V, T, c, r) on ℝⁿ, applied to directions supported on V; reason: for h vanishing off V this is the directional derivative in the active coordinates
--   - encoding: g_* ∈ ℝ^V and h ∈ ℝ^V a unit vector → g_* ∈ ℝⁿ arbitrary; h vanishing off V with Σ_j h_j² = 1; reason: for h vanishing off V, g_*·h depends only on the V coordinates of g_*
--   - generalization: m ≥ 1 (the standing assumption of Theorem 1.1) → m = 0 also allowed; reason: with no rows there are no row constraints and the row sums are empty; the source's cases m ≥ 1 are included unchanged
--   - reading: "all large-row vectors" → the retained row vectors b_i of the large rows; reason: the proof names "the large-row constraint b_iᵀh = 0" (p.11)
--   - encoding: row, column and sign indices i ∈ [m], j ∈ [n], σ ∈ {−1, 1} → Fin m, Fin n (0-based) and σ : Bool with sgn true = 1, sgn false = −1; reason: Lean conventions; same instances
-- source:
--   S. Guo, E. X. Fang, J. Lu, Vector Balancing in Polynomial Time, arXiv:2609.23540 (held file sha256 b777ade4…), Proposition 4.5, p.10 (PDF p.11)

import Mathlib
import Definitions.Def_VecBalPoly_IsClean
import Definitions.Def_VecBalPoly_Phi

namespace VecBalPoly

open Matrix

/-- **Proposition 4.5 (existence of negative curvature).**
Guo, Fang, Lu, *Vector Balancing in Polynomial Time*, arXiv:2609.23540 (held file sha256
b777ade4…), Proposition 4.5, p.10 (PDF p.11): "At any state after cleanup with s > K and L ≤ 2, for
every g∗ ∈ ℝ^V, there is a unit vector h ∈ ℝ^V orthogonal to g∗, all large-row vectors, and all
nearly tight barrier gradients, such that hᵀ∇²Φ h ≤ −2η."

**Formalization Note** "State after cleanup" is `IsClean`. `h` is supported on `V` with
`∑ hⱼ² = 1`; the large-row vectors are the retained rows `bᵢ` of large rows (p.11: "the
large-row constraint `bᵢᵀh = 0`"); the nearly tight barrier gradients are `g_{iσ}` for medium
rows with `u_{iσ} ≥ −1`. Since `h` vanishes off `V`, testing `g⋆ ⬝ h = 0` for all
`g⋆ ∈ ℝⁿ` is the same as for all `g⋆ ∈ ℝ^V`. -/
theorem proposition_4_5 :
    ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (st : St m n), IsClean A st →
      K < (st.V.card : ℝ) → L A st ≤ 2 →
      ∀ gstar : Fin n → ℝ, ∃ h : Fin n → ℝ, (∀ j, j ∉ st.V → h j = 0) ∧ ∑ j, h j ^ 2 = 1 ∧
        gstar ⬝ᵥ h = 0 ∧
        (∀ i, IsLarge A st i → b A st i ⬝ᵥ h = 0) ∧
        (∀ i σ, IsMedium A st i → -1 ≤ u A st i σ → gradU A st i σ ⬝ᵥ h = 0) ∧
        d2Phi A st h ≤ -2 * eta n := by sorry

end VecBalPoly
