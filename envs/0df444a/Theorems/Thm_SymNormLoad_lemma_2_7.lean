-- Prove2me | Theorems.Thm_SymNormLoad_lemma_2_7
-- name    : SymNormLoad.lemma_2_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:32:43.189502+00:00
-- url     : https://prove2.me/theorems/e8a74e8e-0e5c-4f24-860c-0a516851428d
-- title:
--   Lemma 2.7 — rank-dependent increment bound $g(L+b)-g(L)\le\frac12\max\{g(L),M/k\}$
-- statement:
--   Let $M\ge2$, $\Psi$ a monotone symmetric norm on $\mathbb R^M$, $\varphi(k)=\Psi(\mathbf 1_k)$, $h$ the load transform and $g=e^h$. If $k\in[M]=\{1,\dots,M\}$ and scalars $L,b\ge0$ satisfy $b\,\varphi(k)\le1$, then
--   $$
--   g(L+b)-g(L)\ \le\ \frac12\max\Bigl\{g(L),\ \frac Mk\Bigr\}.\tag{2.7}
--   $$
--
--   Applied to the offline load of rank $k$, this bounds each machine's potential increase by half its penalty or a rank-dependent allowance $M/(2k)$; summing the allowances costs a harmonic factor.
--
--   Differences from the source:
--   - encoding: the load transform h : [0, ∞) → [0, ∞) defined by (2.2) → any h : ℝ → ℝ with IsLoadTransform Ψ h (h 0 = 0 and the derivative of (2.2) within [0, ∞) at every t ≥ 0); reason: (2.2) has exactly one solution on [0, ∞) (milestone eq_2_2), and values on t < 0 are never used; same h
--   - encoding: a monotone symmetric norm Ψ : ℝ^M → ℝ≥0 with machines 1, …, M → a function Ψ : (Fin M → ℝ) → ℝ with IsMonotoneSymmetricNorm Ψ (norm axioms, permutation invariance, monotonicity on the orthant); machines 0, …, M−1; reason: Lean convention; the same norms, relabelled coordinates
-- source:
--   Chen–Im–Sirri, Online Load Balancing under Symmetric Norms, manuscript (STOC 2027 submission), Lemma 2.7, Eq. (2.7), p.12

import Mathlib
import Definitions.Def_SymNormLoad_IsMonotoneSymmetricNorm
import Definitions.Def_SymNormLoad_IsLoadTransform
import Definitions.Def_SymNormLoad_phi
import Definitions.Def_SymNormLoad_pen

namespace SymNormLoad

/-- **Lemma 2.7 (a rank-dependent increment bound, (2.7)).** Chen–Im–Sirri, *Online Load
Balancing under Symmetric Norms*, manuscript (STOC 2027 submission), Lemma 2.7, p.12. If
`k ∈ [M]` and scalars `L, b ≥ 0` satisfy `b φ(k) ≤ 1`, then
`g(L + b) − g(L) ≤ ½ max{g(L), M/k}`.

**Formalization Note** `g = exp ∘ h` is `pen h`; `[M] = {1, …, M}`; `M/k` is real division with
`k ≥ 1`. `2 ≤ M` is the standing assumption of §1.1. -/
theorem lemma_2_7 (M : ℕ) (hM : 2 ≤ M) (Ψ : (Fin M → ℝ) → ℝ)
    (hΨ : IsMonotoneSymmetricNorm Ψ) (h : ℝ → ℝ) (hh : IsLoadTransform Ψ h)
    (k : ℕ) (hk1 : 1 ≤ k) (hkM : k ≤ M) (L b : ℝ) (hL : 0 ≤ L) (hb : 0 ≤ b)
    (hbk : b * phi Ψ k ≤ 1) :
    pen h (L + b) - pen h L ≤ (1 / 2) * max (pen h L) ((M : ℝ) / k) := by sorry

end SymNormLoad
