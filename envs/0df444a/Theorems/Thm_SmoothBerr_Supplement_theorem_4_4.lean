-- Prove2me | Theorems.Thm_SmoothBerr_Supplement_theorem_4_4
-- name    : SmoothBerr.Supplement.theorem_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:59:59.482354+00:00
-- url     : https://prove2.me/theorems/2c56ffc2-130f-4af6-8be3-5605e0491dad
-- title:
--   Theorem 4.4 — deterministic methods are no better than Krylov on the normal equations: $\sup t_\Phi\ge\frac14(\sup t_{\mathrm{ne}}-1)$
-- statement:
--   Let $\mathcal F\subseteq\mathbb R^{n\times n}$ be a set of invertible matrices closed under orthogonal actions: $U^\top AV\in\mathcal F$ for all $A\in\mathcal F$ and all orthogonal $U,V$. Fix $b\in\mathbb R^n$ and $\varepsilon$. Let $\Phi$ be a deterministic matvec algorithm that, for every $A\in\mathcal F$, halts on $(A,b)$ and returns a vector of backward error at most $\varepsilon$, using $t_\Phi(A,b)$ matvecs. Then
--   $$
--   \sup_{A\in\mathcal F}t_\Phi(A,b)\ \ge\ \frac14\Bigl(\sup_{A\in\mathcal F}t_{\mathrm{ne}}(A,b)-1\Bigr),
--   $$
--   where $t_{\mathrm{ne}}$ is the Krylov benchmark of Eq. (2).
--
--   The theorem reduces lower bounds for arbitrary deterministic algorithms to lower bounds for one Krylov method, and thereby to polynomial approximation (Lemma 4.5, Theorem 4.6).
--
--   **Formalization Note** Both suprema are taken in $\mathbb N\cup\{\infty\}$, and the inequality is written $\sup t_{\mathrm{ne}}\le4\sup t_\Phi+1$, which is the printed one including the infinite cases.
--
--   Differences from the source:
--   - generalization: Φ solves linear systems to backward error ε → Φ is required to halt with backward error ≤ ε only on (A, b) for A ∈ F and the fixed b; reason: the hypothesis is weaker, so the theorem is stronger; it specializes to an algorithm that solves all systems
--   - encoding: sup t_Φ ≥ (1/4)(sup t_ne − 1) → (⨆ A ∈ F, tNe ε A b) ≤ 4 * (⨆ A ∈ F, numMatvecs Φ A b) + 1 in ℕ∞; reason: the same inequality, rearranged; ℕ∞ represents the infinite cases
-- source:
--   Dereziński, Mahoney, Meyer, Musco, From smoothed analysis to backward error: The power of adaptive perturbations (manuscript of 3 Nov 2026, STOC 2027 submission; sha256 9575cd20bc2c854eb092a4950988f7fbef8715adda344a1ba39489bc28b4e58d), Theorem 4.4, p.6

import Mathlib
import Definitions.Def_SmoothBerr_Supplement_BerrLe
import Definitions.Def_SmoothBerr_Supplement_DetMatvecAlg
import Definitions.Def_SmoothBerr_Supplement_tNe

open Matrix

namespace SmoothBerr.Supplement

/-- **Theorem 4.4 (Deterministic methods cannot do better than Krylov on the normal equations)** (Dereziński, Mahoney, Meyer, Musco, *From smoothed analysis to backward error: The power of adaptive perturbations*, manuscript of 3 Nov 2026, sha256 9575cd20…, Theorem 4.4, p.6).

Let `F ⊆ ℝ^{n×n}` be a set of invertible matrices closed under orthogonal actions
(`UᵀAV ∈ F` for all orthogonal `U, V`). Fix `b ∈ ℝⁿ`. Let `Φ` be a deterministic matvec
algorithm that solves the systems `Ax = b`, `A ∈ F`, to backward error `ε`, using `t_Φ(A, b)`
matvecs. Then `sup_{A∈F} t_Φ(A, b) ≥ (1/4)(sup_{A∈F} t_ne(A, b) − 1)`.

**Formalization Note**
1. `t_Φ` (`numMatvecs`) and `t_ne` (Eq. (2), `tNe`) take values in `ℕ∞`; the inequality is
   written `sup t_ne ≤ 4 sup t_Φ + 1`, which is the printed one, including the infinite cases.
2. "Solves to backward error `ε`" is required on `F` and the fixed `b` only: for every
   `A ∈ F`, `Φ` halts on `(A, b)` and its output has `berr ≤ ε` (`BerrLe`). -/
theorem theorem_4_4 (n : ℕ) (F : Set (Matrix (Fin n) (Fin n) ℝ))
    (hF : ∀ A ∈ F, IsUnit A.det)
    (hFinv : ∀ A ∈ F, ∀ U ∈ Matrix.orthogonalGroup (Fin n) ℝ,
      ∀ V ∈ Matrix.orthogonalGroup (Fin n) ℝ, Uᵀ * A * V ∈ F)
    (b : Fin n → ℝ) (ε : ℝ) (Φ : DetMatvecAlg n)
    (hΦ : ∀ A ∈ F, ∃ k : ℕ, Φ.HaltsWithin A b k ∧ BerrLe A b (Φ.outputAt A b k) ε) :
    (⨆ A ∈ F, tNe ε A b) ≤ 4 * (⨆ A ∈ F, Φ.numMatvecs A b) + 1 := by sorry

end SmoothBerr.Supplement
