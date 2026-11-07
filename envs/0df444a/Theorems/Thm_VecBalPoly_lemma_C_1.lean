-- Prove2me | Theorems.Thm_VecBalPoly_lemma_C_1
-- name    : VecBalPoly.lemma_C_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T23:17:03.210292+00:00
-- url     : https://prove2.me/theorems/8dab0279-9f06-4538-ab4a-612062de7ed9
-- title:
--   Lemma C.1 — Taylor bound for the potential, with $H=2^{24}$
-- statement:
--   Let $H=2^{24}$. At every state after coefficient removal and scale updates with $s>K$ and $L\le2$, keeping $V,T_i,c_i,r_i$ fixed,
--   $$\Big|\Phi(x+th)-\Phi(x)-t\langle\nabla\Phi,h\rangle-\frac{t^2}{2}h^{\mathsf T}\nabla^2\Phi h\Big|\le\frac{Hn^2}{6}|t|^3$$
--   for every $h\in\mathbb R^V$ with $\|h\|_2\le1$ and every $t\in[-1/4,1/4]$ for which the segment $\{x+\theta th:\theta\in[0,1]\}$ stays in the cube $[-1,1]^n$.
--
--   Proposition 5.1 applies this bound along each update to show that the potential stays bounded.
--
--   Differences from the source:
--   - generalization: "There is an absolute constant H ≥ 1" → H = 2²⁴; reason: the proof concludes "H = 2²⁴ is admissible" (p.15), the value fixed in §2.4; an explicit H ≥ 1 implies the existence
--   - generalization: a state after cleanup of Algorithm 2.2 → any state satisfying IsClean (cube, V = {|x_j| < 1}, T_i ⊆ V, (2.2), (2.3) on medium rows, column norms ≤ 1); reason: every post-cleanup state of a run satisfies these conditions, and the proof uses only them
--   - encoding: ∇Φ, ∇²Φ with V, T_i, c_i, r_i fixed (gradient in the active coordinates) → Fréchet derivatives (fderiv) of y ↦ Φ(y; V, T, c, r) on ℝⁿ, applied to directions supported on V; reason: for h vanishing off V this is the directional derivative in the active coordinates
--   - encoding: vectors of ℝ^V → vectors of ℝⁿ vanishing off V; reason: same objects; T_i ⊆ V
--   - generalization: m ≥ 1 (the standing assumption of Theorem 1.1) → m = 0 also allowed; reason: with no rows there are no row constraints and the row sums are empty; the source's cases m ≥ 1 are included unchanged
--   - encoding: the segment stays in the cube; ‖h‖₂ ≤ 1 → |x_j + θ t h_j| ≤ 1 for all θ ∈ [0, 1] and all j; Σ_j h_j² ≤ 1; reason: the same conditions written coordinatewise
--   - encoding: indices i ∈ [m], j ∈ [n] → Fin m, Fin n (0-based); reason: Lean convention; same instances
-- source:
--   S. Guo, E. X. Fang, J. Lu, Vector Balancing in Polynomial Time, arXiv:2609.23540 (held file sha256 b777ade4…), Lemma C.1, p.14 (PDF p.15); value of H, p.15 and §2.4, p.6

import Mathlib
import Definitions.Def_VecBalPoly_IsClean
import Definitions.Def_VecBalPoly_Phi

namespace VecBalPoly

/-- **Lemma C.1 (Taylor bound for the potential), with `H = 2²⁴`.**
Guo, Fang, Lu, *Vector Balancing in Polynomial Time*, arXiv:2609.23540 (held file sha256
b777ade4…), Lemma C.1, p.14 (PDF p.15): "There is an absolute constant H ≥ 1 such that, at every state
after coefficient removal and scale updates, with s > K and L ≤ 2, keeping V, Ti, ci, ri fixed,
|Φ(x + th) − Φ(x) − t⟨∇Φ, h⟩ − (t²/2) hᵀ∇²Φh| ≤ (Hn²/6)|t|³ for every h ∈ ℝ^s with ∥h∥2 ≤ 1 and
every t ∈ [−1/4, 1/4] for which the segment stays in the cube." The proof concludes that
`H = 2²⁴` is admissible (p.15), the value fixed in §2.4 (p.6).

**Formalization Note** The constant is the explicit `H = 2²⁴` (`Hc`), which implies the
printed "there is an absolute constant `H ≥ 1`". "State after coefficient removal and scale
updates" is `IsClean`. `Φ(x + th)` is `phiAt` (`V, Tᵢ, cᵢ, rᵢ` fixed); `h` is supported on
`V`; the segment stays in the cube: `|xⱼ + θthⱼ| ≤ 1` for all `θ ∈ [0, 1]` and all `j`. -/
theorem lemma_C_1 :
    ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (st : St m n), IsClean A st →
      K < (st.V.card : ℝ) → L A st ≤ 2 →
      ∀ h : Fin n → ℝ, (∀ j, j ∉ st.V → h j = 0) → ∑ j, h j ^ 2 ≤ 1 →
      ∀ t : ℝ, -1 / 4 ≤ t → t ≤ 1 / 4 →
      (∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ j, |st.x j + θ * t * h j| ≤ 1) →
      |phiAt A st (st.x + t • h) - phiAt A st st.x - t * dPhi A st h -
          t ^ 2 / 2 * d2Phi A st h| ≤ Hc * (n : ℝ) ^ 2 / 6 * |t| ^ 3 := by sorry

end VecBalPoly
