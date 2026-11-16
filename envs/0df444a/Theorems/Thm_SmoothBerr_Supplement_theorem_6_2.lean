-- Prove2me | Theorems.Thm_SmoothBerr_Supplement_theorem_6_2
-- name    : SmoothBerr.Supplement.theorem_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:59:21.641714+00:00
-- url     : https://prove2.me/theorems/e6b2360b-6ce5-4d67-ac43-a785003ba823
-- title:
--   Theorem 6.2 — optimality of Krylov on the normal equations: $\sup t_\Phi\ge\frac14(\sup t_{k\text{-opt}}-1)$
-- statement:
--   Let $(\mathcal F,\mathrm{acc})$ be a general inverse problem (Setting 6.1) and fix $b\in\mathbb R^n$. Let $\Phi$ be a deterministic matvec algorithm such that, for every $A\in\mathcal F$, it halts on $(A,b)$ with $\mathrm{acc}(A,b,\Phi(A,b))=1$, and let $t_\Phi(A,b)$ be the number of matvecs it expends. Then
--   $$
--   \sup_{A\in\mathcal F}t_\Phi(A,b)\ \ge\ \frac14\Bigl(\sup_{A\in\mathcal F}t_{k\text{-opt}}(A,b)-1\Bigr),
--   $$
--   with $t_{k\text{-opt}}$ as in Eq. (19).
--
--   Any orthogonally invariant test of solution quality thus inherits the Krylov benchmark as a deterministic lower bound; Theorem 4.4 is the backward-error instance.
--
--   **Formalization Note** Both suprema are taken in $\mathbb N\cup\{\infty\}$; the inequality is written $\sup t_{k\text{-opt}}\le4\sup t_\Phi+1$.
--
--   Differences from the source:
--   - encoding: acc : ℝ^{n×n} × ℝⁿ × ℝⁿ → {0, 1}; acc(·) = 1 → acc a predicate; acc holds; reason: the same tests
--   - encoding: sup t_Φ ≥ (1/4)(sup t_k-opt − 1) → (⨆ A ∈ F, tKOpt acc A b) ≤ 4 * (⨆ A ∈ F, numMatvecs Φ A b) + 1 in ℕ∞; reason: the same inequality, rearranged; ℕ∞ represents the infinite cases
-- source:
--   Dereziński, Mahoney, Meyer, Musco, From smoothed analysis to backward error: The power of adaptive perturbations (manuscript of 3 Nov 2026, STOC 2027 submission; sha256 9575cd20bc2c854eb092a4950988f7fbef8715adda344a1ba39489bc28b4e58d), Theorem 6.2, p.17

import Mathlib
import Definitions.Def_SmoothBerr_Supplement_DetMatvecAlg
import Definitions.Def_SmoothBerr_Supplement_IsGeneralInverseProblem
import Definitions.Def_SmoothBerr_Supplement_tKOpt

open Matrix

namespace SmoothBerr.Supplement

/-- **Theorem 6.2 (Optimality of Krylov on the normal equations)** (Dereziński, Mahoney, Meyer, Musco, *From smoothed analysis to backward error: The power of adaptive perturbations*, manuscript of 3 Nov 2026, sha256 9575cd20…, Theorem 6.2, p.17).

Instate Setting 6.1 for `(F, acc)`. Fix `b ∈ ℝⁿ`. Let `Φ` be a deterministic matvec algorithm
with `acc(A, b, Φ(A, b)) = 1` for all `A ∈ F`, and let `t_Φ(A, b)` be the number of matvecs it
expends. Then `sup_{A∈F} t_Φ(A, b) ≥ (1/4)(sup_{A∈F} t_k-opt(A, b) − 1)`.

**Formalization Note** `t_Φ` (`numMatvecs`) and `t_k-opt` (Eq. (19), `tKOpt`) take values in
`ℕ∞`; the inequality is written `sup t_k-opt ≤ 4 sup t_Φ + 1`, the printed one including the
infinite cases. The hypothesis on `Φ` includes that it halts on every `(A, b)`, `A ∈ F`. -/
theorem theorem_6_2 (n : ℕ) (F : Set (Matrix (Fin n) (Fin n) ℝ))
    (acc : Matrix (Fin n) (Fin n) ℝ → (Fin n → ℝ) → (Fin n → ℝ) → Prop)
    (hS : IsGeneralInverseProblem F acc) (b : Fin n → ℝ) (Φ : DetMatvecAlg n)
    (hΦ : ∀ A ∈ F, ∃ k : ℕ, Φ.HaltsWithin A b k ∧ acc A b (Φ.outputAt A b k)) :
    (⨆ A ∈ F, tKOpt acc A b) ≤ 4 * (⨆ A ∈ F, Φ.numMatvecs A b) + 1 := by sorry

end SmoothBerr.Supplement
