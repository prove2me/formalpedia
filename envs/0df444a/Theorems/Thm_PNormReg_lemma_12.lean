-- Prove2me | Theorems.Thm_PNormReg_lemma_12
-- name    : PNormReg.lemma_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:39:04.506337+00:00
-- url     : https://prove2.me/theorems/61ec4910-f784-4381-90ca-f77532f0070b
-- title:
--   Lemma 12, p.24 — $\|W^{1/2-1/p}AU\|_{2\to2}\le\xi$ implies $\|AU\|_{2\to p}\le\xi$
-- statement:
--   Let $A$ have full column rank, $p\ge2$, let $W$ contain $\ell_p$ Lewis weight overestimates of $A$, let $U\in\mathbb R^{k\times r}$ and $\xi>0$. If $\|W^{1/2-1/p}AU\|_{2\to2}\le\xi$, then
--
--   $$\|AU\|_{2\to p}\le\xi.$$
--
--   It transfers an operator bound in the weighted Euclidean geometry, which is checked by a Loewner comparison, to the $\ell_2\to\ell_p$ geometry of the game.
--
--   Differences from the source:
--   - generalization: U ∈ ℝ^{k×r}, where k ≤ d → no relation between k and a further d; reason: k ≤ d is not used and d does not occur in the conclusion; the printed statement is an instance
-- source:
--   Adil, Bullins, O'Carroll, Sidford, Solving p-norm regression in matrix multiplication time, STOC 2027 submission (manuscript sha256 e335b2fa…), Lemma 12, p.24 (PDF p.25)

import Mathlib
import Definitions.Def_PNormReg_Norms
import Definitions.Def_PNormReg_Lewis

open Matrix

namespace PNormReg

/-- **Lemma 12**, p.24 (PDF p.25).

Adil, Bullins, O'Carroll, Sidford, *Solving p-norm regression in matrix multiplication time*, STOC 2027
submission (manuscript sha256 e335b2fa…).

"Let U ∈ R^{k×r}, where k ≤ d, satisfy ∥W^{1/2−1/p}AU∥_{2→2} ≤ ξ, where W contains ℓp Lewis weight
overestimates of A and ξ > 0. Then ∥AU∥_{2→p} ≤ ξ."

**Formalization Note.** `p ≥ 2` is the preamble of §3; `A` has full column rank (its `A = NZ`). The
bound `k ≤ d` does not enter. -/
theorem lemma_12 {n k r : ℕ} (A : Matrix (Fin n) (Fin k) ℝ) (hA : Function.Injective A.mulVec)
    (w : Fin n → ℝ) (p ξ : ℝ) (hp : 2 ≤ p) (hw : IsLewisOver A (1 / p) w) (hξ : 0 < ξ)
    (U : Matrix (Fin k) (Fin r) ℝ) (hU : opTwoTo 2 (weightedMat w (1 / 2 - 1 / p) A * U) ≤ ξ) :
    opTwoTo p (A * U) ≤ ξ := by sorry

end PNormReg
