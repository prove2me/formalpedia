-- Prove2me | Theorems.Thm_SymNormLoad_lemma_2_2
-- name    : SymNormLoad.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:30:48.841262+00:00
-- url     : https://prove2.me/theorems/0a2b97d2-4382-41de-8b18-b274f126aa37
-- title:
--   Lemma 2.2 — flat-vector bounds $\max_k x^{\downarrow}_k\varphi(k)\le\Psi(x)\le\int_0^\infty\varphi(N_x(t))\,dt$
-- statement:
--   Let $M\ge2$ and let $\Psi$ be a monotone symmetric norm on $\mathbb R^M$, with $\varphi(k)=\Psi(\mathbf 1_k)$. For $x\in\mathbb R^M_{\ge0}$ let $x^{\downarrow}_k$ be its $k$-th largest coordinate and $N_x(t)=|\{i:x_i>t\}|$. Then
--   $$
--   \max_{k\in[M]}x^{\downarrow}_k\,\varphi(k)\ \le\ \Psi(x)\ \le\ \int_0^\infty\varphi(N_x(t))\,dt.\tag{2.1}
--   $$
--
--   The two bounds reduce a general symmetric norm to its values on flat vectors; the lower bound restricts the offline loads by rank, and the upper bound converts the potential bound into a norm bound.
--
--   Differences from the source:
--   - encoding: a monotone symmetric norm Ψ : ℝ^M → ℝ≥0 with machines 1, …, M → a function Ψ : (Fin M → ℝ) → ℝ with IsMonotoneSymmetricNorm Ψ (norm axioms, permutation invariance, monotonicity on the orthant); machines 0, …, M−1; reason: Lean convention; the same norms, relabelled coordinates
--   - encoding: max_{k∈[M]} x↓_k φ(k) ≤ Ψ(x) → ∀ k, 1 ≤ k → k ≤ M → kthLargest x k * phi Ψ k ≤ Ψ x; reason: a maximum over a finite set is at most Ψ(x) exactly when every term is
--   - encoding: ∫_0^∞ φ(N_x(t)) dt → Bochner integral ∫ t in Set.Ioi 0, phi Ψ (countAbove x t); reason: the integrand is a bounded step function vanishing for t ≥ max_i x_i, hence integrable; the endpoint 0 is a null set
-- source:
--   Chen–Im–Sirri, Online Load Balancing under Symmetric Norms, manuscript (STOC 2027 submission), Lemma 2.2, Eq. (2.1), p.9

import Mathlib
import Definitions.Def_SymNormLoad_IsMonotoneSymmetricNorm
import Definitions.Def_SymNormLoad_phi
import Definitions.Def_SymNormLoad_kthLargest
import Definitions.Def_SymNormLoad_countAbove

namespace SymNormLoad

/-- **Lemma 2.2 (flat-vector bounds, (2.1)).** Chen–Im–Sirri, *Online Load Balancing under
Symmetric Norms*, manuscript (STOC 2027 submission), Lemma 2.2, p.9. For `x ∈ ℝ^M_{≥0}`, with
`x↓_k` its `k`-th largest coordinate and `N_x(t) = |{i : x_i > t}|`,
`max_{k ∈ [M]} x↓_k φ(k) ≤ Ψ(x) ≤ ∫_0^∞ φ(N_x(t)) dt`.

**Formalization Note** The maximum over `k ∈ [M]` is stated as "for every `1 ≤ k ≤ M`", which is
equivalent. The integral is the Bochner integral over `(0, ∞)`; its integrand is bounded and
vanishes for `t ≥ max_i x_i`, so it is integrable. `2 ≤ M` is the standing assumption of §1.1. -/
theorem lemma_2_2 (M : ℕ) (hM : 2 ≤ M) (Ψ : (Fin M → ℝ) → ℝ)
    (hΨ : IsMonotoneSymmetricNorm Ψ) (x : Fin M → ℝ) (hx : 0 ≤ x) :
    (∀ k : ℕ, 1 ≤ k → k ≤ M → kthLargest x k * phi Ψ k ≤ Ψ x) ∧
      Ψ x ≤ ∫ t in Set.Ioi (0 : ℝ), phi Ψ (countAbove x t) := by sorry

end SymNormLoad
