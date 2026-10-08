-- Prove2me | Theorems.Thm_ShorNonsmooth_SpaceDilation_gTilde_inner_adjoint_identity
-- name    : ShorNonsmooth.SpaceDilation.gTilde_inner_adjoint_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-04T20:27:33.504445+00:00
-- url     : https://prove2.me/theorems/7299f142-1a74-47b4-9cb9-45df849ed831
-- title:
--   Step 0 of Theorem 3.3: $\langle \tilde g_k, A_k v \rangle = \langle g(x_k), v \rangle$ — the substitution that removes $A_k$
-- statement:
--   Write $\tilde g_k = B_k^{*} g(x_k)$, where $B_k^{*}$ is the adjoint of $B_k$, and let $A_k$ be the companion operator with $B_k A_k = I$ (the Proved theorem `sdg_B_comp_A`). Then for every $v$,
--
--   $$\langle \tilde g_k, A_k v \rangle = \langle B_k^{*} g(x_k), A_k v \rangle = \langle g(x_k), \, B_k (A_k v) \rangle = \langle g(x_k), v \rangle.$$
--
--   The second equality is the defining adjoint symmetry $\langle T^{*}y, x\rangle = \langle y, Tx\rangle$ in a real inner-product space, and the third is the non-stalling hypothesis, which supplies $B_k A_k = I$.
--
--   **Why this single identity is the crux of Theorem 3.3.** The proof of Theorem 3.3 (Shor 1985, pp. 56-57) needs the scalar $\gamma_k = \langle u_k, \xi_k\rangle$ with $u_k = A_k(x_k - x^{*})$ and $\xi_k = \tilde g_k/\|\tilde g_k\|$. This identity gives $\langle \tilde g_k, u_k\rangle = \langle g(x_k), x_k - x^{*}\rangle$ exactly, so $\gamma_k = \frac{P}{\|\tilde g_k\|}$ with $P = \langle g(x_k), x_k-x^{*}\rangle$. That is precisely the quantity bounded by assumption (3.18), which is why the theorem's one-step estimate is a consequence of (3.18) alone and never needs the value of $A_k$ or any finite-dimensionality hypothesis. Without it, the whole argument would be circular, since $\langle \tilde g_k, A_k v\rangle$ cannot be reduced to $\langle g(x_k), v\rangle$ from $A_k B_k = I$ alone.
-- source:
--   Shor, Extensions of Subgradient Methods for Minimization (1985), pp. 55-56: $\langle B^{*} g, A v\rangle = \langle g, v\rangle$ for $BA = I$, used to obtain $\langle \tilde g_k, u_k\rangle = \langle g(x_k), x_k - x^{*}\rangle$ in the proof of Theorem 3.3.

import Mathlib
import Definitions.Def_ShorNonsmooth_SpaceDilation_SDGMethod

open ShorNonsmooth.SpaceDilation

namespace ShorNonsmooth.SpaceDilation

/-- If the SDG run has not stalled before index `k` (i.e. `g (sdg … j).x ≠ 0` for all `j < k`),
then for every `v`

    ⟨g̃_k, A_k v⟩ = ⟨g(x_k), v⟩.

This is Step 0 of the proof of Theorem 3.3 (pp. 56-57): it is what lets the inner product
`⟨g̃_k, u_k⟩` with `u_k = A_k(x_k - x*)` be computed without knowing `A_k` explicitly, which is
the reason the theorem's step estimate needs only (3.18) and not the `A`-metric. -/
theorem gTilde_inner_adjoint_identity {n : ℕ} (hn : 0 < n)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (h : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ)
    (α : ℕ → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n))
    (B₀ : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (δ : ℝ) (hδ : 0 < δ)
    (hα : ∀ k : ℕ, 1 ≤ k → 1 + δ ≤ α k)
    (k : ℕ) (hstop : ∀ j : ℕ, j < k → g (sdg g h α x₀ B₀ j).x ≠ 0)
    (v : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (gTilde g h α x₀ B₀ k) ((sdg g h α x₀ B₀ k).A v)
      = inner ℝ (g (sdg g h α x₀ B₀ k).x) v := by
  sorry

end ShorNonsmooth.SpaceDilation
