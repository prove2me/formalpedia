-- Prove2me | Theorems.Thm_VecBalPoly_lemma_D_1
-- name    : VecBalPoly.lemma_D_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T23:17:30.355192+00:00
-- url     : https://prove2.me/theorems/25557570-bee3-499e-8b10-6871ebc54a3c
-- title:
--   Lemma D.1 — approximating the gradient and Hessian
-- statement:
--   There is a deterministic real-RAM procedure with the following property. Given a state after coefficient removal and scale updates with $s>K$, $L\le2$ and $u_{i\sigma}\le0$ for every medium pair, and given $0<\epsilon<1$, it computes $\tilde g\in\mathbb R^V$ and a symmetric $\tilde H$ on $\mathbb R^V$ with
--   $$\|\tilde g-\nabla\Phi\|_2\le\epsilon,\qquad\|\tilde H-\nabla^2\Phi\|_{\mathrm{op}}\le\epsilon,$$
--   using $O\big(mn^2+(n^3+m)\log(2mn/\epsilon)\big)$ real arithmetic operations and comparisons, with a constant independent of $m$, $n$, $A$, the state and $\epsilon$.
--
--   **Formalization Note** Here $\epsilon$ is the lemma's own accuracy input, appended to the state's listing. The outputs are $\tilde g$ ($n$ cells) followed by $\tilde H$ ($n\times n$, row by row); only the $V$ coordinates are tested. The operator norm bound is tested on every $h$ supported on $V$.
--
--   Differences from the source:
--   - generalization: a state after cleanup of Algorithm 2.2 → any state satisfying IsClean (cube, V = {|x_j| < 1}, T_i ⊆ V, (2.2), (2.3) on medium rows, column norms ≤ 1); reason: every post-cleanup state of a run satisfies these conditions, and the proof uses only them
--   - reading: "a deterministic procedure" / "can be implemented" in the unit-cost real-RAM model (no machine fixed) → one program of the published MatMulTimeLP.RealRAM, Admissible (rational literals; +, −, ×, ÷, comparisons; no square root, no random draw), chosen before the instance and correct on every tape; reason: these are exactly the operations of Proposition 2.3; without draws the run does not depend on the tape
--   - reading: no bound on m printed → m ≥ 1; reason: the paper's standing assumption (Theorem 1.1: "given any m, n ≥ 1"); log(2mn/ϵ) is undefined at m = 0
--   - encoding: O(mn² + (n³ + m) log(2mn/ϵ)) real arithmetic operations and comparisons, for 0 < ϵ < 1 → one constant C (with the program, before the instance) bounding realOps, the number of executed radd, rsub, rmul, rdiv and rblt instructions, and the run halts; reason: O(·) uniform over instances; the paper counts real arithmetic operations and comparisons only
--   - encoding: ‖H̃ − ∇²Φ‖_op ≤ ϵ on ℝ^V, H̃ symmetric → H̃ symmetric on V × V and ‖P_V (H̃ − ∇²Φ) h‖₂ ≤ ϵ‖h‖₂ for every h supported on V; reason: the operator norm on ℝ^V, written by testing every vector
--   - encoding: ∇Φ, ∇²Φ with V, T_i, c_i, r_i fixed (gradient in the active coordinates) → Fréchet derivatives (fderiv) of y ↦ Φ(y; V, T, c, r) on ℝⁿ, applied to directions supported on V; reason: for h vanishing off V this is the directional derivative in the active coordinates
--   - encoding: the procedure is given the current state and ϵ; outputs g̃ and H̃ → input stateLayout followed by ϵ; g̃ in the first n output cells, H̃ row by row in the next n × n; reason: a direct listing of the state; the paper fixes no layout
--   - encoding: row, column and sign indices i ∈ [m], j ∈ [n], σ ∈ {−1, 1} → Fin m, Fin n (0-based) and σ : Bool with sgn true = 1, sgn false = −1; reason: Lean conventions; same instances
-- source:
--   S. Guo, E. X. Fang, J. Lu, Vector Balancing in Polynomial Time, arXiv:2609.23540 (held file sha256 b777ade4…), Lemma D.1 and (D.1), p.15 (PDF p.16)

import Mathlib
import Definitions.Def_MatMulTimeLP_RealRAM
import Definitions.Def_VecBalPoly_Admissible
import Definitions.Def_VecBalPoly_realOps
import Definitions.Def_VecBalPoly_stateLayout
import Definitions.Def_VecBalPoly_IsClean
import Definitions.Def_VecBalPoly_Phi

namespace VecBalPoly

open Matrix

/-- **Lemma D.1 (approximating the gradient and Hessian).**
Guo, Fang, Lu, *Vector Balancing in Polynomial Time*, arXiv:2609.23540 (held file sha256
b777ade4…), Lemma D.1, p.15 (PDF p.16): "At a state after coefficient removal and scale updates, with
s > K, L ≤ 2 and uiσ ≤ 0 for every medium pair, one can compute g̃ and a symmetric H̃ satisfying
(D.1) in O(mn² + (n³ + m) log(2mn/ϵ)) real arithmetic operations and comparisons, for
0 < ϵ < 1." with (D.1): "∥g̃ − ∇Φ∥2 ≤ ϵ, ∥H̃ − ∇²Φ∥op ≤ ϵ."

**Formalization Note** One admissible program `P` and one constant `C`, chosen before the
instance. Here `ϵ` is the lemma's own input, appended to the state's listing. "State after
coefficient removal and scale updates" is `IsClean`; `m ≥ 1` is the paper's standing
assumption (Theorem 1.1). The output cells hold `g̃` (`n` cells) and then `H̃` (`n × n`, row by
row). `H̃` is symmetric on `V × V`; the error of `g̃` is the Euclidean norm on `V`; the
operator norm on `ℝ^V` is bounded by testing every `h` supported on `V`. -/
theorem lemma_D_1 :
    ∃ P : MatMulTimeLP.Program, Admissible P ∧ ∃ C : ℝ,
      ∀ (m n : ℕ), 1 ≤ m → ∀ (A : Matrix (Fin m) (Fin n) ℝ) (st : St m n) (ϵ : ℝ),
        IsClean A st → K < (st.V.card : ℝ) → L A st ≤ 2 →
        (∀ i σ, IsMedium A st i → u A st i σ ≤ 0) → 0 < ϵ → ϵ < 1 →
        ∀ ω : MatMulTimeLP.Tape, ∃ t : ℕ,
          MatMulTimeLP.HaltsAt P (stateLayout A st ++ [ϵ]) ω t ∧
          (realOps P (stateLayout A st ++ [ϵ]) ω t : ℝ) ≤
            C * ((m : ℝ) * (n : ℝ) ^ 2 + ((n : ℝ) ^ 3 + m) * Real.log (2 * m * n / ϵ)) ∧
          (∀ j ∈ st.V, ∀ k ∈ st.V,
            MatMulTimeLP.outputMatAt P (stateLayout A st ++ [ϵ]) ω t n n n j k =
              MatMulTimeLP.outputMatAt P (stateLayout A st ++ [ϵ]) ω t n n n k j) ∧
          Real.sqrt (∑ j ∈ st.V,
            (MatMulTimeLP.outputAt P (stateLayout A st ++ [ϵ]) ω t n j - gradPhi A st j) ^ 2)
            ≤ ϵ ∧
          ∀ h : Fin n → ℝ, (∀ j, j ∉ st.V → h j = 0) →
            Real.sqrt (∑ j ∈ st.V,
              ((MatMulTimeLP.outputMatAt P (stateLayout A st ++ [ϵ]) ω t n n n - hessPhi A st)
                *ᵥ h) j ^ 2) ≤ ϵ * Real.sqrt (∑ j, h j ^ 2) := by sorry

end VecBalPoly
