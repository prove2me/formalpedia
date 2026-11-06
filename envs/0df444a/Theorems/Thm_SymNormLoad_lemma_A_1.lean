-- Prove2me | Theorems.Thm_SymNormLoad_lemma_A_1
-- name    : SymNormLoad.lemma_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:33:57.285218+00:00
-- url     : https://prove2.me/theorems/0655ab59-a70a-4b4d-86d0-8df1e805a6c2
-- title:
--   Lemma A.1 — unit-scale guarantee $\Phi(L)\le T_M$, $\Psi(L)\le\Gamma_M$
-- statement:
--   Let $M\ge2$, $\Psi$ a monotone symmetric norm on $\mathbb R^M$, $h$ the load transform, $\Phi(x)=\sum_ie^{h(x_i)}$, $c=\ln(3/2)$ and
--   $$
--   T_M=M(1+H_M),\qquad \Gamma_M=\frac{\ln M+H_M}{c}.
--   $$
--   If the jobs $p_1,\dots,p_N\in\mathbb R^M_{\ge0}$ of a run admit an integral assignment of norm at most $1$, then the final load vector $L$ of the greedy Algorithm 2.4 satisfies
--   $$
--   \Phi(L)\le T_M\qquad\text{and}\qquad\Psi(L)\le\Gamma_M.
--   $$
--
--   This is the guarantee of one phase of the doubling algorithm that proves Theorem 2.1.
--
--   Differences from the source:
--   - encoding: T_M := M(1 + H_M) and Γ_M = (ln M + H_M)/c → written out in the statement; reason: same values
--   - encoding: the jobs admit an integral assignment of norm at most 1 → ∃ σ : Fin N → Fin M, Ψ (loadVec p σ) ≤ 1; reason: an integral assignment is a map from jobs to machines; its load vector is loadVec p σ
--   - encoding: the final load vector L of Algorithm 2.4 (ties to the smallest index) → greedyLoad h p: the loads after running the step of (2.4) on jobs 0, …, N−1, ties to the least element of Fin M; reason: the same algorithm, 0-based indices
--   - encoding: H_M = Σ_{k=1}^M 1/k → (harmonic M : ℝ), Mathlib's harmonic number cast from ℚ; reason: same value
--   - encoding: jobs 1, …, N with processing times p_{ji} ≥ 0 → jobs Fin N (0-based), p : Fin N → Fin M → ℝ with ∀ j i, 0 ≤ p j i; reason: relabelling; the same instances
--   - encoding: the load transform h : [0, ∞) → [0, ∞) defined by (2.2) → any h : ℝ → ℝ with IsLoadTransform Ψ h (h 0 = 0 and the derivative of (2.2) within [0, ∞) at every t ≥ 0); reason: (2.2) has exactly one solution on [0, ∞) (milestone eq_2_2), and values on t < 0 are never used; same h
--   - encoding: a monotone symmetric norm Ψ : ℝ^M → ℝ≥0 with machines 1, …, M → a function Ψ : (Fin M → ℝ) → ℝ with IsMonotoneSymmetricNorm Ψ (norm axioms, permutation invariance, monotonicity on the orthant); machines 0, …, M−1; reason: Lean convention; the same norms, relabelled coordinates
-- source:
--   Chen–Im–Sirri, Online Load Balancing under Symmetric Norms, manuscript (STOC 2027 submission), Lemma A.1, p.38 (with Γ_M defined on p.38)

import Mathlib
import Definitions.Def_SymNormLoad_IsMonotoneSymmetricNorm
import Definitions.Def_SymNormLoad_IsLoadTransform
import Definitions.Def_SymNormLoad_loadVec
import Definitions.Def_SymNormLoad_Phi__cbe170
import Definitions.Def_SymNormLoad_greedyLoad

namespace SymNormLoad

/-- **Lemma A.1 (unit-scale guarantee).** Chen–Im–Sirri, *Online Load Balancing under Symmetric
Norms*, manuscript (STOC 2027 submission), Lemma A.1, p.38. With
`Γ_M = (ln M + H_M)/c`, `c = ln(3/2)` (p.38): if the jobs in a run admit an integral assignment of
norm at most `1`, then the greedy algorithm (2.4) gives `Φ(L) ≤ T_M := M(1 + H_M)` and
`Ψ(L) ≤ Γ_M`.

**Formalization Note** `T_M` and `Γ_M` are written out. "Admit an integral assignment of norm at
most 1" is `∃ σ, Ψ (loadVec p σ) ≤ 1`; `L = greedyLoad h p`. `2 ≤ M` is the standing assumption
of §1.1. -/
theorem lemma_A_1 (M : ℕ) (hM : 2 ≤ M) (Ψ : (Fin M → ℝ) → ℝ)
    (hΨ : IsMonotoneSymmetricNorm Ψ) (h : ℝ → ℝ) (hh : IsLoadTransform Ψ h)
    (N : ℕ) (p : Fin N → Fin M → ℝ) (hp : ∀ j i, 0 ≤ p j i)
    (hopt : ∃ σ : Fin N → Fin M, Ψ (loadVec p σ) ≤ 1) :
    Phi h (greedyLoad h p) ≤ (M : ℝ) * (1 + (harmonic M : ℝ)) ∧
      Ψ (greedyLoad h p) ≤ (Real.log M + (harmonic M : ℝ)) / Real.log (3 / 2) := by sorry

end SymNormLoad
