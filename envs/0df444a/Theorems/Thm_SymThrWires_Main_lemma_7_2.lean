-- Prove2me | Theorems.Thm_SymThrWires_Main_lemma_7_2
-- name    : SymThrWires.Main.lemma_7_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:15:54.288401+00:00
-- url     : https://prove2.me/theorems/73ce1681-c930-43b0-8eda-762a7b56c721
-- title:
--   Lemma 7.2 — moment certificates: Σ v(x)^{2K} < R₀^{2K} forces |v| < R₀, and conversely when √2 R′ < R₀
-- statement:
--   Let $K\ge1$ be an integer, $V$ a finite set with $|V|\le2^K$, $v:V\to\mathbb Z$, and $R_0\ge1$ an integer. If
--   $$\sum_{x\in V}v(x)^{2K}<R_0^{2K},$$
--   then $|v(x)|<R_0$ for all $x\in V$. Conversely, if $|v|\le R'$ on $V$ and $\sqrt2\,R'<R_0$, then $\sum_{x\in V}v(x)^{2K}<R_0^{2K}$.
--
--   A single power sum certifies a uniform bound on a whole column of integer values, and honest values pass the test; this is how the algorithm checks guessed digits without trusting the witness.
--
--   Differences from the source: none.
-- source:
--   Dev Nag, Near-Cubic Gate and Near-Quartic Wire Lower Bounds for SYM∘THR Circuits, STOC 2027 submission, Zenodo doi:10.5281/zenodo.23847026 (sha256 02f54f02…), p. 21, Lemma 7.2

import Mathlib

namespace SymThrWires.Main

/-- **Lemma 7.2** (Moment certificates, p. 21). Let `K ≥ 1`, `V` a finite set with `|V| ≤ 2^K`,
`v : V → Z` and `R₀ ≥ 1` an integer. If `Σ_x v(x)^{2K} < R₀^{2K}` then `|v(x)| < R₀` for all `x`;
conversely, if `|v| ≤ R′` on `V` and `√2 R′ < R₀`, then `Σ_x v(x)^{2K} < R₀^{2K}`. -/
theorem lemma_7_2 {V : Type} [Fintype V] (K : ℕ) (hK : 1 ≤ K) (hV : Fintype.card V ≤ 2 ^ K)
    (v : V → ℤ) (R₀ : ℤ) (hR₀ : 1 ≤ R₀) :
    (∑ x, v x ^ (2 * K) < R₀ ^ (2 * K) → ∀ x, |v x| < R₀) ∧
    (∀ R' : ℝ, (∀ x, |(v x : ℝ)| ≤ R') → Real.sqrt 2 * R' < (R₀ : ℝ) →
      ∑ x, v x ^ (2 * K) < R₀ ^ (2 * K)) := by sorry

end SymThrWires.Main
