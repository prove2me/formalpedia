-- Prove2me | Theorems.Thm_SmoothBerr_Supplement_theorem_6_4
-- name    : SmoothBerr.Supplement.theorem_6_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:58:41.344636+00:00
-- url     : https://prove2.me/theorems/4250a78f-da97-4ea7-aab2-49e5eeb1ee8f
-- title:
--   Theorem 6.4 — optimality of Krylov on the normal equations, alternating version: $\sup t_\Phi\ge\frac12(\sup t_{k\text{-opt}}-1)$
-- statement:
--   Let $(\mathcal F,\mathrm{acc})$ be a general inverse problem (Setting 6.1) and fix $b\in\mathbb R^n$. Let $\Phi$ be a deterministic **alternating** matvec algorithm (Definition 6.3) such that, for every $A\in\mathcal F$, it halts on $(A,b)$ with $\mathrm{acc}(A,b,\Phi(A,b))=1$. Then
--   $$
--   \sup_{A\in\mathcal F}t_\Phi(A,b)\ \ge\ \frac12\Bigl(\sup_{A\in\mathcal F}t_{k\text{-opt}}(A,b)-1\Bigr).
--   $$
--
--   For alternating algorithms the comparison with the Krylov benchmark loses only the factor $2$ that building $R_k(A,b)$ costs; Theorem 6.2 follows by simulating an arbitrary algorithm by an alternating one.
--
--   **Formalization Note** In $\mathbb N\cup\{\infty\}$ the inequality is written $\sup t_{k\text{-opt}}\le2\sup t_\Phi+1$.
--
--   Differences from the source:
--   - encoding: acc : ℝ^{n×n} × ℝⁿ × ℝⁿ → {0, 1}; acc(·) = 1 → acc a predicate; acc holds; reason: the same tests
--   - encoding: Φ alternating (Definition 6.3) → IsAlternating Φ: the query kind is fixed by the transcript length on every transcript; reason: changing Φ on unreachable transcripts changes no run
--   - encoding: sup t_Φ ≥ (1/2)(sup t_k-opt − 1) → (⨆ A ∈ F, tKOpt acc A b) ≤ 2 * (⨆ A ∈ F, numMatvecs Φ A b) + 1 in ℕ∞; reason: the same inequality, rearranged
-- source:
--   Dereziński, Mahoney, Meyer, Musco, From smoothed analysis to backward error: The power of adaptive perturbations (manuscript of 3 Nov 2026, STOC 2027 submission; sha256 9575cd20bc2c854eb092a4950988f7fbef8715adda344a1ba39489bc28b4e58d), Theorem 6.4, p.17

import Mathlib
import Definitions.Def_SmoothBerr_Supplement_DetMatvecAlg
import Definitions.Def_SmoothBerr_Supplement_IsAlternating
import Definitions.Def_SmoothBerr_Supplement_IsGeneralInverseProblem
import Definitions.Def_SmoothBerr_Supplement_tKOpt

open Matrix

namespace SmoothBerr.Supplement

/-- **Theorem 6.4 (Optimality of Krylov on the normal equations, alternating version)** (Dereziński, Mahoney, Meyer, Musco, *From smoothed analysis to backward error: The power of adaptive perturbations*, manuscript of 3 Nov 2026, sha256 9575cd20…, Theorem 6.4, p.17).

The setup of Theorem 6.2 (Setting 6.1 for `(F, acc)`, a fixed `b`, a deterministic `Φ` with
`acc(A, b, Φ(A, b)) = 1` for all `A ∈ F`), where in addition `Φ` is alternating
(Definition 6.3). Then `sup_{A∈F} t_Φ(A, b) ≥ (1/2)(sup_{A∈F} t_k-opt(A, b) − 1)`.

**Formalization Note** As in Theorem 6.2, in `ℕ∞` the inequality reads
`sup t_k-opt ≤ 2 sup t_Φ + 1`. -/
theorem theorem_6_4 (n : ℕ) (F : Set (Matrix (Fin n) (Fin n) ℝ))
    (acc : Matrix (Fin n) (Fin n) ℝ → (Fin n → ℝ) → (Fin n → ℝ) → Prop)
    (hS : IsGeneralInverseProblem F acc) (b : Fin n → ℝ) (Φ : DetMatvecAlg n)
    (hAlt : IsAlternating Φ)
    (hΦ : ∀ A ∈ F, ∃ k : ℕ, Φ.HaltsWithin A b k ∧ acc A b (Φ.outputAt A b k)) :
    (⨆ A ∈ F, tKOpt acc A b) ≤ 2 * (⨆ A ∈ F, Φ.numMatvecs A b) + 1 := by sorry

end SmoothBerr.Supplement
