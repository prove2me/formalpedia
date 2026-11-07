-- Prove2me | Theorems.Thm_PNormReg_lemma_6
-- name    : PNormReg.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:38:55.718206+00:00
-- url     : https://prove2.me/theorems/5ebeba83-eeec-461f-82e5-258612037cbd
-- title:
--   Lemma 6, p.16 — norm comparisons for Lewis weight overestimates
-- statement:
--   Let $A$ have full column rank, $p\in[1,\infty]$, let $w$ be $\ell_p$ Lewis weight overestimates of $A$, and $W=\mathrm{Diag}(w)$. For all $x$,
--
--   $$\|Ax\|_p\le\|W^{1/2-1/p}Ax\|_2\le\|w\|_1^{1/2-1/p}\|Ax\|_p\quad\text{if }p\in[2,\infty],$$
--
--   $$\|W^{1/2-1/p}Ax\|_2\le\|Ax\|_p\le\|w\|_1^{1/p-1/2}\|W^{1/2-1/p}Ax\|_2\quad\text{if }p\in[1,2].$$
--
--   These comparisons replace the dimension $n$ of the plain $\ell_2$-$\ell_p$ comparison with the number of columns, which is what brings the norm of the game matrix down to $O(\sqrt d)$.
--
--   Differences from the source:
--   - encoding: p ∈ [1, ∞], with 1/p = 0 at p = ∞ → p = ∞ is its own clause, with ∥·∥_∞, W^{1/2} and ∥w∥₁^{1/2}; reason: finite p is a real exponent in Lean; every case of the lemma is stated
-- source:
--   Adil, Bullins, O'Carroll, Sidford, Solving p-norm regression in matrix multiplication time, STOC 2027 submission (manuscript sha256 e335b2fa…), Lemma 6, p.16 (PDF p.17); Definition 4, p.15

import Mathlib
import Definitions.Def_PNormReg_Norms
import Definitions.Def_PNormReg_Lewis

open Matrix

namespace PNormReg

/-- **Lemma 6** (Norm comparisons for Lewis weight overestimates), p.16 (PDF p.17).

Adil, Bullins, O'Carroll, Sidford, *Solving p-norm regression in matrix multiplication time*, STOC 2027
submission (manuscript sha256 e335b2fa…).

For full column rank `A`, overestimates `w` and all `x`:
* for finite `p ≥ 2`, `∥Ax∥_p ≤ ∥W^{1/2−1/p}Ax∥₂ ≤ ∥w∥₁^{1/2−1/p}∥Ax∥_p`;
* for `p = ∞`, `∥Ax∥_∞ ≤ ∥W^{1/2}Ax∥₂ ≤ ∥w∥₁^{1/2}∥Ax∥_∞`;
* for `p ∈ [1, 2]`, `∥W^{1/2−1/p}Ax∥₂ ≤ ∥Ax∥_p ≤ ∥w∥₁^{1/p−1/2}∥W^{1/2−1/p}Ax∥₂`.

**Formalization Note.** `p = ∞` is its own clause with `1/p = 0`. `A` has full column rank by the
standing assumption of §2. -/
theorem lemma_6 {n k : ℕ} (A : Matrix (Fin n) (Fin k) ℝ) (hA : Function.Injective A.mulVec)
    (w : Fin n → ℝ) :
    (∀ p : ℝ, 2 ≤ p → IsLewisOver A (1 / p) w → ∀ x : Fin k → ℝ,
      lpNorm p (A *ᵥ x) ≤ l2Norm (weightedMat w (1 / 2 - 1 / p) A *ᵥ x) ∧
      l2Norm (weightedMat w (1 / 2 - 1 / p) A *ᵥ x) ≤
        (∑ i, w i) ^ (1 / 2 - 1 / p) * lpNorm p (A *ᵥ x)) ∧
    (IsLewisOver A 0 w → ∀ x : Fin k → ℝ,
      linfNorm (A *ᵥ x) ≤ l2Norm (weightedMat w (1 / 2 - 0) A *ᵥ x) ∧
      l2Norm (weightedMat w (1 / 2 - 0) A *ᵥ x) ≤
        (∑ i, w i) ^ (1 / 2 : ℝ) * linfNorm (A *ᵥ x)) ∧
    (∀ p : ℝ, 1 ≤ p → p ≤ 2 → IsLewisOver A (1 / p) w → ∀ x : Fin k → ℝ,
      l2Norm (weightedMat w (1 / 2 - 1 / p) A *ᵥ x) ≤ lpNorm p (A *ᵥ x) ∧
      lpNorm p (A *ᵥ x) ≤
        (∑ i, w i) ^ (1 / p - 1 / 2) * l2Norm (weightedMat w (1 / 2 - 1 / p) A *ᵥ x)) := by sorry

end PNormReg
