-- Prove2me | Theorems.Thm_SymNormLoad_corollary_2_8
-- name    : SymNormLoad.corollary_2_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:32:53.29224+00:00
-- url     : https://prove2.me/theorems/f1510655-e40a-409e-a7c0-9f5b9fb87128
-- title:
--   Corollary 2.8 — adding a load vector of norm at most one
-- statement:
--   Let $M\ge2$, $\Psi$ a monotone symmetric norm on $\mathbb R^M$, $h$ the load transform and $\Phi(x)=\sum_i e^{h(x_i)}$. For $L,z\in\mathbb R^M_{\ge0}$ with $\Psi(z)\le1$,
--   $$
--   \Phi(L+z)-\Phi(L)\ \le\ \frac12\Phi(L)+\frac M2\,(H_M-1),\tag{2.8}
--   $$
--   where $H_M=\sum_{k=1}^M1/k$ is the $M$-th harmonic number.
--
--   Differences from the source:
--   - encoding: H_M = Σ_{k=1}^M 1/k → (harmonic M : ℝ), Mathlib's harmonic number cast from ℚ; reason: same value
--   - encoding: the load transform h : [0, ∞) → [0, ∞) defined by (2.2) → any h : ℝ → ℝ with IsLoadTransform Ψ h (h 0 = 0 and the derivative of (2.2) within [0, ∞) at every t ≥ 0); reason: (2.2) has exactly one solution on [0, ∞) (milestone eq_2_2), and values on t < 0 are never used; same h
--   - encoding: a monotone symmetric norm Ψ : ℝ^M → ℝ≥0 with machines 1, …, M → a function Ψ : (Fin M → ℝ) → ℝ with IsMonotoneSymmetricNorm Ψ (norm axioms, permutation invariance, monotonicity on the orthant); machines 0, …, M−1; reason: Lean convention; the same norms, relabelled coordinates
-- source:
--   Chen–Im–Sirri, Online Load Balancing under Symmetric Norms, manuscript (STOC 2027 submission), Corollary 2.8, Eq. (2.8), p.13

import Mathlib
import Definitions.Def_SymNormLoad_IsMonotoneSymmetricNorm
import Definitions.Def_SymNormLoad_IsLoadTransform
import Definitions.Def_SymNormLoad_Phi__cbe170

namespace SymNormLoad

/-- **Corollary 2.8 (adding a load vector of norm at most one, (2.8)).** Chen–Im–Sirri, *Online
Load Balancing under Symmetric Norms*, manuscript (STOC 2027 submission), Corollary 2.8, p.13. For
`L, z ∈ ℝ^M_{≥0}` with `Ψ(z) ≤ 1`, `Φ(L + z) − Φ(L) ≤ ½ Φ(L) + (M/2)(H_M − 1)`.

**Formalization Note** `H_M = ∑_{k=1}^M 1/k` is Mathlib's `harmonic M` (a rational, cast to `ℝ`).
`2 ≤ M` is the standing assumption of §1.1. -/
theorem corollary_2_8 (M : ℕ) (hM : 2 ≤ M) (Ψ : (Fin M → ℝ) → ℝ)
    (hΨ : IsMonotoneSymmetricNorm Ψ) (h : ℝ → ℝ) (hh : IsLoadTransform Ψ h)
    (L z : Fin M → ℝ) (hL : 0 ≤ L) (hz : 0 ≤ z) (hΨz : Ψ z ≤ 1) :
    Phi h (L + z) - Phi h L ≤
      (1 / 2) * Phi h L + ((M : ℝ) / 2) * ((harmonic M : ℝ) - 1) := by sorry

end SymNormLoad
