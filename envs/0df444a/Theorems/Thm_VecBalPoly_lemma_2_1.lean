-- Prove2me | Theorems.Thm_VecBalPoly_lemma_2_1
-- name    : VecBalPoly.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T23:17:41.770678+00:00
-- url     : https://prove2.me/theorems/df85e4fc-8501-44bd-a371-33ffd67595fb
-- title:
--   Lemma 2.1 — computing an update direction
-- statement:
--   There is a deterministic real-RAM procedure with the following property. At any state after cleanup with $s=|V|>K$, $L\le2$ and $u_{i\sigma}\le0$ for every medium row and sign, it computes, using polynomially many real arithmetic operations and comparisons, a direction $h\in\mathbb R^V$ satisfying the large-row constraints and the nearly tight barrier constraints, together with
--   $$\tfrac12\le\|h\|_2\le1,\qquad|\langle\nabla\Phi,h\rangle|\le\epsilon,\qquad h^{\mathsf T}\nabla^2\Phi h\le-\frac{3\eta}{16},$$
--   where $\epsilon=\eta\tau/K^2$.
--
--   This is the step that makes the algorithm implementable: it turns the existence of negative curvature (Proposition 4.5) into a computed direction.
--
--   **Formalization Note** The procedure reads the state's data from its input; "polynomially many" means at most $C(m+n+2)^k$ with $C,k$ fixed before the instance.
--
--   Differences from the source:
--   - generalization: a state after cleanup of Algorithm 2.2 → any state satisfying IsClean (cube, V = {|x_j| < 1}, T_i ⊆ V, (2.2), (2.3) on medium rows, column norms ≤ 1); reason: every post-cleanup state of a run satisfies these conditions, and the proof uses only them
--   - reading: "a deterministic procedure" / "can be implemented" in the unit-cost real-RAM model (no machine fixed) → one program of the published MatMulTimeLP.RealRAM, Admissible (rational literals; +, −, ×, ÷, comparisons; no square root, no random draw), chosen before the instance and correct on every tape; reason: these are exactly the operations of Proposition 2.3; without draws the run does not depend on the tape
--   - encoding: "polynomially many real arithmetic operations and comparisons" (bounded by C(m + n + 2)^k) → one constant C (with the program, before the instance) bounding realOps, the number of executed radd, rsub, rmul, rdiv and rblt instructions, and the run halts; reason: O(·) uniform over instances; the paper counts real arithmetic operations and comparisons only
--   - encoding: the procedure is given the current state → input stateLayout (A, x, indicator of V, indicators of T_i, c, r); h in the first n output cells; reason: a direct listing of the state; the paper fixes no layout
--   - encoding: ∇Φ, ∇²Φ with V, T_i, c_i, r_i fixed (gradient in the active coordinates) → Fréchet derivatives (fderiv) of y ↦ Φ(y; V, T, c, r) on ℝⁿ, applied to directions supported on V; reason: for h vanishing off V this is the directional derivative in the active coordinates
--   - generalization: m ≥ 1 (the standing assumption of Theorem 1.1) → m = 0 also allowed; reason: with no rows there are no row constraints and the row sums are empty; the source's cases m ≥ 1 are included unchanged
--   - encoding: h ∈ ℝ^V → h ∈ ℝⁿ vanishing off V (first clause of GoodDir); reason: same objects; T_i ⊆ V
--   - encoding: row, column and sign indices i ∈ [m], j ∈ [n], σ ∈ {−1, 1} → Fin m, Fin n (0-based) and σ : Bool with sgn true = 1, sgn false = −1; reason: Lean conventions; same instances
-- source:
--   S. Guo, E. X. Fang, J. Lu, Vector Balancing in Polynomial Time, arXiv:2609.23540 (held file sha256 b777ade4…), Lemma 2.1, p.6 (PDF p.7); proof in Appendix D.3, p.18

import Mathlib
import Definitions.Def_MatMulTimeLP_RealRAM
import Definitions.Def_VecBalPoly_Admissible
import Definitions.Def_VecBalPoly_realOps
import Definitions.Def_VecBalPoly_stateLayout
import Definitions.Def_VecBalPoly_IsClean
import Definitions.Def_VecBalPoly_GoodDir

namespace VecBalPoly

/-- **Lemma 2.1 (computing an update direction).**
Guo, Fang, Lu, *Vector Balancing in Polynomial Time*, arXiv:2609.23540 (held file sha256
b777ade4…), Lemma 2.1, p.6 (PDF p.7): "At any state after cleanup with s > K, L ≤ 2, and all
medium-row barriers nonpositive, a deterministic procedure finds h ∈ ℝ^V satisfying the large-row
and nearly tight barrier constraints, together with 1/2 ≤ ∥h∥2 ≤ 1, |⟨∇Φ, h⟩| ≤ ϵ,
hᵀ∇²Φh ≤ −3η/16. The procedure uses polynomially many real arithmetic operations and
comparisons."

**Formalization Note** One admissible program `P` and constants `C, k`, chosen before the
instance. "A state after cleanup" is `IsClean` (the structural conditions such states satisfy).
On the listing `stateLayout A st` of the state and every tape, `P` halts after at most
`C(m + n + 2)^k` real arithmetic operations and comparisons, and its first `n` output cells are
a direction with all the guarantees (`GoodDir`, with `ϵ = ητ/K²`). -/
theorem lemma_2_1 :
    ∃ P : MatMulTimeLP.Program, Admissible P ∧ ∃ C k : ℕ,
      ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (st : St m n), IsClean A st →
        K < (st.V.card : ℝ) → L A st ≤ 2 →
        (∀ i σ, IsMedium A st i → u A st i σ ≤ 0) →
        ∀ ω : MatMulTimeLP.Tape, ∃ t : ℕ, MatMulTimeLP.HaltsAt P (stateLayout A st) ω t ∧
          realOps P (stateLayout A st) ω t ≤ C * (m + n + 2) ^ k ∧
          GoodDir A st (MatMulTimeLP.outputAt P (stateLayout A st) ω t n) := by sorry

end VecBalPoly
