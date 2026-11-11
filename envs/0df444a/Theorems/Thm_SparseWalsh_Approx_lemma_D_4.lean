-- Prove2me | Theorems.Thm_SparseWalsh_Approx_lemma_D_4
-- name    : SparseWalsh.Approx.lemma_D_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:02:25.297996+00:00
-- url     : https://prove2.me/theorems/2a305ebf-05f2-43e5-b5ef-f8d889e20a64
-- title:
--   Lemma D.4 — selection with s or 2s terms: bounds (11), (12) and the specializations (13)
-- statement:
--   Let $f:\mathbb F_2^d\to\mathbb R$ and $s\ge1$. Let $T$ be the support of an optimal $s$-term approximation of $f$ and $\tau^2=\sum_{a\notin T}\hat f(a)^2$. Let $W$ be a candidate set, $\rho\ge0$, and $\tilde f$ estimates with $|\tilde f(a)-\hat f(a)|\le\rho$ for all $a\in W$. Put $\mu=\sum_{a\in T\setminus W}\hat f(a)^2$. For $j\in\{s,2s\}$, let $A_j$ contain the $j$ elements of $W$ with the largest estimated magnitudes, or all of $W$ if $|W|<j$, with fixed tie-breaking, and set $h_j=\sum_{a\in A_j}\tilde f(a)\chi_a$. Then
--   $$\|f-h_s\|_2^2\le\tau^2+\mu+4\rho\sqrt s\,\tau+5s\rho^2\qquad(11)$$
--   and
--   $$\|f-h_{2s}\|_2^2\le\tau^2+\mu+10s\rho^2.\qquad(12)$$
--   In particular, for $0<\varepsilon\le1$ with $\mu\le\varepsilon\tau^2/32$, the bound $\|f-h_j\|_2^2\le(1+\varepsilon)\tau^2$ (13) holds for $j=s$ when $\rho=\varepsilon\tau/(16\sqrt s)$, and for $j=2s$ when $\rho=\sqrt\varepsilon\,\tau/(4\sqrt s)$. This is the final selection step of Algorithm 3. It turns coverage (Lemma 5.2) and accurate final estimates (Lemma D.5) into the guarantee (2).
--
--   Differences from the source:
--
--   - generalization: fixed tie-breaking → every fixed order, given by an injective key into ℕ (smaller key wins); reason: every fixed order on the finite cube is of this form; the paper’s order is one
--   - reading: ε in (13) → 0 < ε ≤ 1, quantified inside the statement; reason: ε is the accuracy of Theorem 5.1, ε ∈ (0, 1]; the proof uses ε ≤ 1 ("each at most ε for 0 < ε ≤ 1")
--   - encoding: T the support of an optimal s-term approximation; τ; f̃ defined on W → IsOptimalSupport s f T; τ = √(Σ_{a∉T} f̂(a)²); ft : Cube d → ℝ, whose values off W are never used (A_j ⊆ W); reason: same objects
--   - generalization: standing assumptions d ≥ 1 and 1 ≤ s ≤ 2^d (Theorem 5.1, Algorithm 3) → every d and every s ≥ 1 (no upper bound s ≤ 2^d); reason: for s > 2^d the set W has fewer than s elements, so A_j = W and the error is at most μ + |W|ρ², which meets (11) and (12); the statement specializes to the source's range
-- source:
--   Attias, Bshouty, Medvedev, Srebro, Efficient Non-Adaptive Sparse Fourier Learning on the Boolean Cube and Finite Abelian Groups, STOC 2027 submission (manuscript sha256 4cbf9075…), p. 43 (PDF p. 46), Lemma D.4; proof pp. 43-44

import Mathlib
import Definitions.Def_SparseWalsh_Approx_Fourier

open scoped BigOperators Matrix

namespace SparseWalsh.Approx

/-- **Lemma D.4** (Selection with s or 2s terms), p. 43 (PDF p. 46). `T` is the support of an
optimal `s`-term approximation of `f` and `τ = (Σ_{a ∉ T} f̂(a)²)^{1/2}`. Let `W` be a candidate set,
`ρ ≥ 0`, and `|f̃(a) − f̂(a)| ≤ ρ` for all `a ∈ W`; `µ = Σ_{a ∈ T∖W} f̂(a)²`. For `j ∈ {s, 2s}`,
`A_j` holds the `j` largest estimated magnitudes `|f̃|` in `W` (all of `W` if `|W| < j`), ties
broken by a fixed order (an injective `key`), and `h_j = Σ_{a ∈ A_j} f̃(a)χ_a`. Then (11)
`‖f − h_s‖₂² ≤ τ² + µ + 4ρ√s τ + 5sρ²` and (12) `‖f − h_{2s}‖₂² ≤ τ² + µ + 10sρ²`; and, for
`0 < ε ≤ 1` with `µ ≤ ετ²/32`, (13) `‖f − h_j‖₂² ≤ (1 + ε)τ²` holds for `j = s` when
`ρ = ετ/(16√s)` and for `j = 2s` when `ρ = √ε τ/(4√s)`. -/
theorem lemma_D_4 {d : ℕ} (s : ℕ) (hs : 1 ≤ s) (f : Cube d → ℝ)
    (T : Finset (Cube d)) (hT : IsOptimalSupport s f T) (key : Cube d → ℕ)
    (hkey : Function.Injective key) (W : Finset (Cube d)) (ft : Cube d → ℝ) (ρ : ℝ)
    (hρ : 0 ≤ ρ) (hacc : ∀ a ∈ W, |ft a - hat f a| ≤ ρ) :
    let τ : ℝ := Real.sqrt (tailSq f T)
    let μ : ℝ := ∑ a ∈ T \ W, hat f a ^ 2
    let h : ℕ → Cube d → ℝ := fun j => polyOn (selectTop key j W ft) ft
    normSq (f - h s) ≤ τ ^ 2 + μ + 4 * ρ * Real.sqrt s * τ + 5 * s * ρ ^ 2 ∧
    normSq (f - h (2 * s)) ≤ τ ^ 2 + μ + 10 * s * ρ ^ 2 ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 → μ ≤ ε * τ ^ 2 / 32 →
      (ρ = ε * τ / (16 * Real.sqrt s) → normSq (f - h s) ≤ (1 + ε) * τ ^ 2) ∧
      (ρ = Real.sqrt ε * τ / (4 * Real.sqrt s) →
        normSq (f - h (2 * s)) ≤ (1 + ε) * τ ^ 2) := by sorry

end SparseWalsh.Approx
