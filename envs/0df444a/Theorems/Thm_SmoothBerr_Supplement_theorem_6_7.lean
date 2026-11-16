-- Prove2me | Theorems.Thm_SmoothBerr_Supplement_theorem_6_7
-- name    : SmoothBerr.Supplement.theorem_6_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:57:58.312763+00:00
-- url     : https://prove2.me/theorems/1cc99b23-2dba-4688-a088-e0306832932a
-- title:
--   Theorem 6.7 — Krylov methods can simulate deterministic methods: $Vz\in R_k(A,b)$
-- statement:
--   Fix $A\in\mathbb R^{n\times n}$, $b\in\mathbb R^n$ and a deterministic alternating matvec algorithm $\Phi$, and let $d=\dim R_n(A,b)$ be the grade of $A$ with respect to $b$. There exist orthogonal matrices $U,V\in\mathbb R^{n\times n}$ with $Ub=b$ such that, for $B=U^\top AV$: if $z=\Phi(B,b)$ is returned after computing $k<d$ matvecs, then
--   $$
--   Vz\in R_k(A,b).
--   $$
--
--   Up to rotations that fix the right-hand side, the output of any alternating algorithm that stops before exhausting the grade lies in the right-side Krylov subspace of the same depth. This is the resisting-oracle step behind Theorems 6.2, 6.4 and 4.4.
--
--   **Formalization Note** $U$ and $V$ depend on $A$, $b$ and $\Phi$ but not on $k$. "Returned after computing $k$ matvecs" means $t_\Phi(B,b)=k$, and $z$ is the output on the final transcript. $A$ need not be invertible.
--
--   Differences from the source:
--   - encoding: z = Φ(B, b) returned after computing k matvecs → numMatvecs Φ B b = k and z = outputAt Φ B b k; reason: the same event and output
--   - encoding: Φ alternating; the grade d → IsAlternating Φ; grade A b = finrank of rightKrylov A b n; reason: Definitions 6.3 and 6.6
-- source:
--   Dereziński, Mahoney, Meyer, Musco, From smoothed analysis to backward error: The power of adaptive perturbations (manuscript of 3 Nov 2026, STOC 2027 submission; sha256 9575cd20bc2c854eb092a4950988f7fbef8715adda344a1ba39489bc28b4e58d), Theorem 6.7, p.18

import Mathlib
import Definitions.Def_SmoothBerr_Supplement_DetMatvecAlg
import Definitions.Def_SmoothBerr_Supplement_IsAlternating
import Definitions.Def_SmoothBerr_Supplement_rightKrylov
import Definitions.Def_SmoothBerr_Supplement_grade

open Matrix

namespace SmoothBerr.Supplement

/-- **Theorem 6.7 (Krylov methods can simulate deterministic methods)** (Dereziński, Mahoney, Meyer, Musco, *From smoothed analysis to backward error: The power of adaptive perturbations*, manuscript of 3 Nov 2026, sha256 9575cd20…, Theorem 6.7, p.18).

Fix any `A ∈ ℝ^{n×n}`, `b ∈ ℝⁿ` and deterministic alternating matvec algorithm `Φ`, and let `d`
be the grade of `A` with respect to `b`. There exist orthogonal `U, V` with `Ub = b` such that,
for `B = UᵀAV`: if `z = Φ(B, b)` is returned after computing `k < d` matvecs, then
`V z ∈ R_k(A, b)`.

**Formalization Note** `U, V` depend on `A`, `b` and `Φ`, and are chosen before `k`. "Returned
after computing `k` matvecs" is `t_Φ(B, b) = k` (`numMatvecs`), and `z` is the output on the
transcript after `k` rounds. `A` is arbitrary (not assumed invertible). -/
theorem theorem_6_7 (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (Φ : DetMatvecAlg n) (hAlt : IsAlternating Φ) :
    ∃ U ∈ Matrix.orthogonalGroup (Fin n) ℝ, ∃ V ∈ Matrix.orthogonalGroup (Fin n) ℝ,
      U *ᵥ b = b ∧
      ∀ k : ℕ, k < grade A b → Φ.numMatvecs (Uᵀ * A * V) b = k →
        V *ᵥ Φ.outputAt (Uᵀ * A * V) b k ∈ rightKrylov A b k := by sorry

end SmoothBerr.Supplement
