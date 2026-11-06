-- Prove2me | Theorems.Thm_SymNormLoad_lemma_2_10
-- name    : SymNormLoad.lemma_2_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:33:38.706726+00:00
-- url     : https://prove2.me/theorems/05c1961b-116a-4ce0-a495-f016444ee117
-- title:
--   Lemma 2.10 — recovering the objective $\Psi(x)\le\frac1c\bigl(\ln M+\frac{\Phi(x)-M}{M}\bigr)$
-- statement:
--   Let $M\ge2$, $\Psi$ a monotone symmetric norm on $\mathbb R^M$, $h$ the load transform, $\Phi(x)=\sum_ie^{h(x_i)}$ and $c=\ln(3/2)$. For every $x\in\mathbb R^M_{\ge0}$,
--   $$
--   \Psi(x)\ \le\ \frac1c\Bigl(\ln M+\frac{\Phi(x)-M}{M}\Bigr).\tag{2.10}
--   $$
--
--   This converts a bound on the potential into a bound on the objective.
--
--   Differences from the source:
--   - encoding: the load transform h : [0, ∞) → [0, ∞) defined by (2.2) → any h : ℝ → ℝ with IsLoadTransform Ψ h (h 0 = 0 and the derivative of (2.2) within [0, ∞) at every t ≥ 0); reason: (2.2) has exactly one solution on [0, ∞) (milestone eq_2_2), and values on t < 0 are never used; same h
--   - encoding: a monotone symmetric norm Ψ : ℝ^M → ℝ≥0 with machines 1, …, M → a function Ψ : (Fin M → ℝ) → ℝ with IsMonotoneSymmetricNorm Ψ (norm axioms, permutation invariance, monotonicity on the orthant); machines 0, …, M−1; reason: Lean convention; the same norms, relabelled coordinates
-- source:
--   Chen–Im–Sirri, Online Load Balancing under Symmetric Norms, manuscript (STOC 2027 submission), Lemma 2.10, Eq. (2.10), p.13

import Mathlib
import Definitions.Def_SymNormLoad_IsMonotoneSymmetricNorm
import Definitions.Def_SymNormLoad_IsLoadTransform
import Definitions.Def_SymNormLoad_Phi__cbe170

namespace SymNormLoad

/-- **Lemma 2.10 (recovering the objective, (2.10)).** Chen–Im–Sirri, *Online Load Balancing under
Symmetric Norms*, manuscript (STOC 2027 submission), Lemma 2.10, p.13. For every
`x ∈ ℝ^M_{≥0}`, `Ψ(x) ≤ (1/c)(ln M + (Φ(x) − M)/M)` with `c = ln(3/2)`.

**Formalization Note** `ln` is `Real.log`; its arguments `M ≥ 2` and `3/2` are positive. `2 ≤ M`
is the standing assumption of §1.1. -/
theorem lemma_2_10 (M : ℕ) (hM : 2 ≤ M) (Ψ : (Fin M → ℝ) → ℝ)
    (hΨ : IsMonotoneSymmetricNorm Ψ) (h : ℝ → ℝ) (hh : IsLoadTransform Ψ h)
    (x : Fin M → ℝ) (hx : 0 ≤ x) :
    Ψ x ≤ (1 / Real.log (3 / 2)) * (Real.log M + (Phi h x - M) / M) := by sorry

end SymNormLoad
