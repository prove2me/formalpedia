-- Prove2me | Theorems.Thm_UhlmannRoof_RankTwo_lemma_6
-- name    : UhlmannRoof.RankTwo.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:34:29.721981+00:00
-- url     : https://prove2.me/theorems/c2849dbe-8051-45dd-8c88-2c027cb82a5d
-- title:
--   Lemma 6, p. 9 — equivalent characterizations of a symmetric optimal pair
-- statement:
--   Let $D$ be the density operator of a rank two state, and let $U$ be a transposition of two minimal diagonal projections that leaves $D$ invariant. The following conditions are equivalent:
--
--   1. $D$ is the only $U$-invariant state in $\Omega_D$.
--   2. $D$ has an optimal decomposition into two different pure states with positive weights, and some member of $\Omega_D$ does not commute with $U$.
--   3. The extreme points of $\Omega_D$ are exactly two states $\rho$ and $U^*\rho U$, interchanged by $U$.
--
--   Here $\Omega_D$ is the intersection of **all** contact sets of affine functionals supporting $R$ at $D$; $R$ is the convex roof of the diagonal entropy over pure state decompositions. This characterizes when the optimal two-state decomposition and the symmetry of the full contact set coincide.
--
--   **Formalization Note** The transposition is explicitly self-adjoint, $U^*=U$, as used in the paper's proof. The two pure states in clause 2 are distinct and both coefficients are positive. The printed proof of (b)$\Rightarrow$(c) is incomplete; the statement is posed as printed. The indices of the swapped projections are arbitrary distinct members of `Fin d`.
-- source:
--   Uhlmann, arXiv:quant-ph/9704017v2, p. 9, Lemma 6 (proof pp. 9–11)

import Mathlib
import Definitions.Def_UhlmannRoof_RankTwo_Model

namespace UhlmannRoof.RankTwo

/-- Uhlmann, Lemma 6, p. 9. The explicit self-adjointness assumption on U
records the author's use of `U = U*` for the transposition. -/
theorem lemma_6 {d : ℕ} (D : Mat d) (hD : IsState D) (hrk : D.rank = 2)
    (U : Mat d) (i j : Fin d) (hU : IsTransposition U i j)
    (hUsa : Matrix.conjTranspose U = U)
    (hinv : Matrix.conjTranspose U * D * U = D) :
    List.TFAE
      [∀ ν ∈ OmegaOf D, Matrix.conjTranspose U * ν * U = ν → ν = D,
       (∃ (p : ℝ) (ρ₁ ρ₂ : Mat d),
          0 < p ∧ p < 1 ∧ IsPure ρ₁ ∧ IsPure ρ₂ ∧ ρ₁ ≠ ρ₂ ∧
          D = (p : ℂ) • ρ₁ + (((1 - p : ℝ) : ℂ) • ρ₂) ∧
          R D = p * Stilde ρ₁ + (1 - p) * Stilde ρ₂) ∧
         ∃ ν ∈ OmegaOf D, ν * U ≠ U * ν,
       ∃ ρ : Mat d, Matrix.conjTranspose U * ρ * U ≠ ρ ∧
         Set.extremePoints ℝ (OmegaOf D) =
           {ρ, Matrix.conjTranspose U * ρ * U}] := by sorry

end UhlmannRoof.RankTwo
