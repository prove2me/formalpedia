-- Prove2me | Theorems.Thm_SymNormLoad_lemma_2_9
-- name    : SymNormLoad.lemma_2_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:33:13.837921+00:00
-- url     : https://prove2.me/theorems/313bcaa6-99f1-4630-bcfa-f587ecacbbd1
-- title:
--   Lemma 2.9 — bounding the potential $\Phi(L)\le M(1+H_M)$
-- statement:
--   Let $M\ge2$, $\Psi$ a monotone symmetric norm on $\mathbb R^M$, $h$ the load transform and $\Phi(x)=\sum_ie^{h(x_i)}$. Let $p_1,\dots,p_N\in\mathbb R^M_{\ge0}$ be jobs that admit an integral assignment of norm at most $1$. Then the final load vector $L$ of the greedy Algorithm 2.4 on these jobs satisfies
--   $$
--   \Phi(L)\ \le\ M(1+H_M).\tag{2.9}
--   $$
--
--   Differences from the source:
--   - encoding: the jobs admit an integral assignment of norm at most 1 → ∃ σ : Fin N → Fin M, Ψ (loadVec p σ) ≤ 1; reason: an integral assignment is a map from jobs to machines; its load vector is loadVec p σ
--   - encoding: the final load vector L of Algorithm 2.4 (ties to the smallest index) → greedyLoad h p: the loads after running the step of (2.4) on jobs 0, …, N−1, ties to the least element of Fin M; reason: the same algorithm, 0-based indices
--   - encoding: H_M = Σ_{k=1}^M 1/k → (harmonic M : ℝ), Mathlib's harmonic number cast from ℚ; reason: same value
--   - encoding: jobs 1, …, N with processing times p_{ji} ≥ 0 → jobs Fin N (0-based), p : Fin N → Fin M → ℝ with ∀ j i, 0 ≤ p j i; reason: relabelling; the same instances
--   - encoding: the load transform h : [0, ∞) → [0, ∞) defined by (2.2) → any h : ℝ → ℝ with IsLoadTransform Ψ h (h 0 = 0 and the derivative of (2.2) within [0, ∞) at every t ≥ 0); reason: (2.2) has exactly one solution on [0, ∞) (milestone eq_2_2), and values on t < 0 are never used; same h
--   - encoding: a monotone symmetric norm Ψ : ℝ^M → ℝ≥0 with machines 1, …, M → a function Ψ : (Fin M → ℝ) → ℝ with IsMonotoneSymmetricNorm Ψ (norm axioms, permutation invariance, monotonicity on the orthant); machines 0, …, M−1; reason: Lean convention; the same norms, relabelled coordinates
-- source:
--   Chen–Im–Sirri, Online Load Balancing under Symmetric Norms, manuscript (STOC 2027 submission), Lemma 2.9, Eq. (2.9), p.13

import Mathlib
import Definitions.Def_SymNormLoad_IsMonotoneSymmetricNorm
import Definitions.Def_SymNormLoad_IsLoadTransform
import Definitions.Def_SymNormLoad_loadVec
import Definitions.Def_SymNormLoad_Phi__cbe170
import Definitions.Def_SymNormLoad_greedyLoad

namespace SymNormLoad

/-- **Lemma 2.9 (bounding the potential, (2.9)).** Chen–Im–Sirri, *Online Load Balancing under
Symmetric Norms*, manuscript (STOC 2027 submission), Lemma 2.9, p.13. If the jobs admit an
integral assignment of norm at most `1`, then the greedy algorithm's final load vector `L`
satisfies `Φ(L) ≤ M(1 + H_M)`.

**Formalization Note** "Admit an integral assignment of norm at most 1" is
`∃ σ, Ψ (loadVec p σ) ≤ 1`. The greedy algorithm (Algorithm 2.4) runs on `p` itself.
`H_M` is `harmonic M` cast to `ℝ`. `2 ≤ M` is the standing assumption of §1.1. -/
theorem lemma_2_9 (M : ℕ) (hM : 2 ≤ M) (Ψ : (Fin M → ℝ) → ℝ)
    (hΨ : IsMonotoneSymmetricNorm Ψ) (h : ℝ → ℝ) (hh : IsLoadTransform Ψ h)
    (N : ℕ) (p : Fin N → Fin M → ℝ) (hp : ∀ j i, 0 ≤ p j i)
    (hopt : ∃ σ : Fin N → Fin M, Ψ (loadVec p σ) ≤ 1) :
    Phi h (greedyLoad h p) ≤ (M : ℝ) * (1 + (harmonic M : ℝ)) := by sorry

end SymNormLoad
