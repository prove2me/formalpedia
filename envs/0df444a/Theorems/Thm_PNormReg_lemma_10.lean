-- Prove2me | Theorems.Thm_PNormReg_lemma_10
-- name    : PNormReg.lemma_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:40:16.621071+00:00
-- url     : https://prove2.me/theorems/f9d31cc2-ff6c-478c-b86f-073dececeb1e
-- title:
--   Lemma 10, p.22 — the scaled problem (19) has optimum at most 1, $\lambda_\xi\tilde u$ is $(16/\lambda_\xi)$-approximate, and $\bar h^\top\bar D^{-1}\bar h\ge2/3$
-- statement:
--   Let $A$ have full column rank, $D\succeq0$, $p\ge2$, $\phi(u)=h^\top u-u^\top Du-\|Au\|_p^p$, and let $w$ be $\ell_p$ Lewis weight overestimates of $A$ with $s=\|w\|_1$. Let $\zeta$ be such that $\phi^\star\in(\zeta/2,\zeta]$. Then the problem
--
--   $$\min_u\|\bar Au\|_p\quad\text{s.t.}\quad-\bar h^\top u+u^\top\bar Du\le-\frac18\tag{19}$$
--
--   has optimum at most 1. Further, if $\tilde u$ is feasible for (19) with $\|\bar A\tilde u\|_p\le\xi$ for some $\xi\ge1$, then $\phi(\lambda_\xi\tilde u)\ge(\lambda_\xi/16)\phi^\star$. Finally, $\bar h^\top\bar D^{-1}\bar h\ge2/3$.
--
--   This normalizes the residual problem to a norm-minimization with unit optimum, losing a factor depending on $p$ and $\xi$ only.
--
--   Differences from the source:
--   - encoding: "has optimum at most 1" → ∃ u feasible for (19) with ∥Āu∥_p ≤ 1; reason: the meaning of the claim for a minimization
--   - encoding: "(16/λ_ξ)-approximate solution to (18)" → φ(λ_ξũ) ≥ (λ_ξ/16)φ⋆; reason: the optimizer conventions of p.7 for maximization
--   - encoding: "s := ∥w∥₁ ≤ 2d" → s = ∥w∥₁; the bound is not a hypothesis; reason: it follows from Definition 4 for A with k ≤ d columns and is unused in the conclusion
-- source:
--   Adil, Bullins, O'Carroll, Sidford, Solving p-norm regression in matrix multiplication time, STOC 2027 submission (manuscript sha256 e335b2fa…), Lemma 10, p.22 (PDF p.23)

import Mathlib
import Definitions.Def_PNormReg_Scaled

open Matrix

namespace PNormReg

/-- **Lemma 10**, p.22 (PDF p.23).

Adil, Bullins, O'Carroll, Sidford, *Solving p-norm regression in matrix multiplication time*, STOC 2027
submission (manuscript sha256 e335b2fa…).

Let `A` have full column rank, `D ⪰ 0`, `w` be `ℓ_p` Lewis weight overestimates of `A`, and
`φ⋆ ∈ (ζ/2, ζ]`. Then problem (19) has optimum at most 1, that is, some `u` satisfies the constraint with
`∥Āu∥_p ≤ 1`; every `ũ` satisfying the constraint with `∥Āũ∥_p ≤ ξ`, `ξ ≥ 1`, has
`φ(λ_ξũ) ≥ (λ_ξ/16)φ⋆`; and `h̄⊤D̄^{−1}h̄ ≥ 2/3`.

**Formalization Note.** "(16/λ_ξ)-approximate" is `φ ≥ φ⋆/(16/λ_ξ)` (optimizer conventions, p.7). The
page's `s ≤ 2d` is not a hypothesis: it follows from `IsLewisOver` (`s ≤ 2k`) and `k ≤ d`. -/
theorem lemma_10 {n k : ℕ} (A : Matrix (Fin n) (Fin k) ℝ) (hA : Function.Injective A.mulVec)
    (D : Matrix (Fin k) (Fin k) ℝ) (hD : D.PosSemidef) (h : Fin k → ℝ) (w : Fin n → ℝ) (p ζ : ℝ)
    (hp : 2 ≤ p) (hw : IsLewisOver A (1 / p) w) (hζ₁ : ζ / 2 < phiStar h D A p)
    (hζ₂ : phiStar h D A p ≤ ζ) :
    (∃ u : Fin k → ℝ, scaledConstraint (scaledH h ζ) (scaledD A D h w p ζ) u ≤ -(1 / 8) ∧
      lpNorm p (scaledA A p ζ *ᵥ u) ≤ 1) ∧
    (∀ (ξ : ℝ) (ut : Fin k → ℝ), 1 ≤ ξ →
      scaledConstraint (scaledH h ζ) (scaledD A D h w p ζ) ut ≤ -(1 / 8) →
      lpNorm p (scaledA A p ζ *ᵥ ut) ≤ ξ →
      (lambdaXi p ξ / 16) * phiStar h D A p ≤ phi h D A p (lambdaXi p ξ • ut)) ∧
    2 / 3 ≤ scaledH h ζ ⬝ᵥ ((scaledD A D h w p ζ)⁻¹ *ᵥ scaledH h ζ) := by sorry

end PNormReg
