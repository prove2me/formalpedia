-- Prove2me | Theorems.Thm_SymNormLoad_lemma_2_3
-- name    : SymNormLoad.lemma_2_3
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T01:31:42.356725+00:00
-- url     : https://prove2.me/theorems/55b5d60e-370b-4c6c-8ae5-90ff2d3a80f7
-- title:
--   Lemma 2.3 — $\varphi$ is nondecreasing and $\varphi(s)/s$ nonincreasing
-- statement:
--   Let $M\ge2$, $\Psi$ a monotone symmetric norm on $\mathbb R^M$, and $\varphi:[0,M]\to\mathbb R$ the piecewise-linear extension of $k\mapsto\Psi(\mathbf 1_k)$. Then
--
--   1. $\varphi(s)$ is nondecreasing on $[0,M]$;
--   2. $\varphi(s)/s$ is nonincreasing on $(0,M]$.
--
--   These two shape properties are what make the load transform increasing, concave, and with convex exponential, and they drive the case analysis of Lemma 2.10.
--
--   Differences from the source:
--   - encoding: a monotone symmetric norm Ψ : ℝ^M → ℝ≥0 with machines 1, …, M → a function Ψ : (Fin M → ℝ) → ℝ with IsMonotoneSymmetricNorm Ψ (norm axioms, permutation invariance, monotonicity on the orthant); machines 0, …, M−1; reason: Lean convention; the same norms, relabelled coordinates
-- source:
--   Chen–Im–Sirri, Online Load Balancing under Symmetric Norms, manuscript (STOC 2027 submission), Lemma 2.3, p.9

import Mathlib
import Definitions.Def_SymNormLoad_IsMonotoneSymmetricNorm
import Definitions.Def_SymNormLoad_phiBar

namespace SymNormLoad

/-- **Lemma 2.3 (monotonicity and decreasing ratio).** Chen–Im–Sirri, *Online Load Balancing
under Symmetric Norms*, manuscript (STOC 2027 submission), Lemma 2.3, p.9. The function `φ(s)`
(the piecewise-linear extension of `k ↦ Ψ(1_k)`) is nondecreasing on `[0, M]`, and `φ(s)/s` is
nonincreasing on `(0, M]`.

**Formalization Note** `φ(s)` is `phiBar Ψ s`, the interpolation of p.9. `2 ≤ M` is the standing
assumption of §1.1. -/
theorem lemma_2_3 (M : ℕ) (hM : 2 ≤ M) (Ψ : (Fin M → ℝ) → ℝ)
    (hΨ : IsMonotoneSymmetricNorm Ψ) :
    MonotoneOn (phiBar Ψ) (Set.Icc 0 (M : ℝ)) ∧
      AntitoneOn (fun s => phiBar Ψ s / s) (Set.Ioc 0 (M : ℝ)) := by sorry

end SymNormLoad
