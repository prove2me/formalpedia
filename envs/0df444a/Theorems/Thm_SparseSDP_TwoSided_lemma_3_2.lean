-- Prove2me | Theorems.Thm_SparseSDP_TwoSided_lemma_3_2
-- name    : SparseSDP.TwoSided.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:53:09.826687+00:00
-- url     : https://prove2.me/theorems/09812955-3c03-4d26-b42f-ab3f7efcb653
-- title:
--   Lemma 3.2, p. 23 — range, second moment and bias of the clipped estimator
-- statement:
--   Under the assumptions of Lemma 3.1, let $R,B>0$ and $X=R\psi\psi^\dagger$. Then
--
--   1. $|\hat Z_{A,B}|\le B$;
--   2. $\mathbb E_I[\hat Z_{A,B}^2]\le R^2\omega^2$;
--   3. $|\mathbb E_I[\hat Z_{A,B}]-\langle A,X\rangle|\le R^2\omega^2/B$.
--
--   Clipping gives the online learner bounded feedback at a small bias.
--
--   Differences from the source:
--   - generalization: $A\in\mathbb C^{n\times n}$ → any `RCLike` scalar field; reason: Algorithm 7 uses the real case; it specializes to $\mathbb C$
--   - generalization: item 1 almost surely → item 1 for every coordinate; reason: `clip` bounds every value
--   - encoding: $\mathbb E_I$ → the finite sum $\sum_i|[\psi]_i|^2(\cdot)$; reason: definition of the expectation for this law
-- source:
--   Brandão, Dalzell, Gilyén, Vasconcelos, Solving Sparse SDPs in Sublinear Time, arXiv:2609.40302, Lemma 3.2, p. 23

import Mathlib
import Definitions.Def_SparseSDP_TwoSided_gap
import Definitions.Def_SparseSDP_TwoSided_zHat

open Matrix
open scoped Matrix.Norms.L2Operator

namespace SparseSDP.TwoSided

/-- **Lemma 3.2** (Properties of the Clipped Estimator), p. 23.

Brandão, Dalzell, Gilyén, Vasconcelos, *Solving Sparse SDPs in Sublinear Time*, arXiv:2609.40302,
Lemma 3.2, p. 23.

Under the assumptions of Lemma 3.1, with `R, B > 0` and `X = Rψψ†`. The bound of item 1 holds for
every coordinate, not only almost surely. -/
theorem lemma_3_2 {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (A : Matrix (Fin n) (Fin n) 𝕜) (ψ : Fin n → 𝕜)
    (ω R B : ℝ) (hA : A.IsHermitian) (hω : ‖A‖ ≤ ω) (hψ : ∑ i, ‖ψ i‖ ^ 2 = 1)
    (hR : 0 < R) (hB : 0 < B) :
    (∀ i, |zHat A ψ R B i| ≤ B) ∧
    ∑ i, ‖ψ i‖ ^ 2 * zHat A ψ R B i ^ 2 ≤ R ^ 2 * ω ^ 2 ∧
    |∑ i, ‖ψ i‖ ^ 2 * zHat A ψ R B i - hs A ((R : 𝕜) • vecMulVec ψ (star ψ))| ≤
      R ^ 2 * ω ^ 2 / B := by sorry

end SparseSDP.TwoSided
