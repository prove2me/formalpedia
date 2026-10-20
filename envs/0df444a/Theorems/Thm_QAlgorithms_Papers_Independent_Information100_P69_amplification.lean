-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P69_amplification
-- name    : QAlgorithms.Papers.Independent.Information100.P69.amplification
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:57:27.810165+00:00
-- url     : https://prove2.me/theorems/86aa58ed-940a-434e-a782-ff01b4b1b92b
-- title:
--   Amplification from vanishing error
-- statement:
--   Assume convex CPTP block sets, tensor closure F2, and a faithful replacer F3. Let $r_0\ge0$ be finite. Along positive lengths $k_j\to\infty$, suppose $L_j$ are CPTP, $M_j\in\mathcal F_{k_j}$, and $\lambda_j\ge1$, with
--   $$L_j\le_{\rm CP}\lambda_jM_j,\quad\|L_j-\mathcal N^{\otimes k_j}\|_\diamond\to0,\quad\limsup_{j\to\infty}\frac{\log_2\lambda_j}{k_j}\le r_0.$$
--   For every $S>r_0$, the exponentially accurate CPTP approximations and free dominators of (5) exist at every sufficiently large integer length. Compactness is not assumed. This amplifies a subsequence approximation and includes exact padding of the other lengths.
--
--   The testing model uses one normalized pure input, possibly entangled across uses and with a reference, and one acceptance effect shared by every alternative. The symbol $\le_{\rm CP}$ means that the difference of the larger and smaller maps is completely positive; $\|\cdot\|_\diamond$ is the full diamond norm. Information quantities use base-2 logarithms.
-- source:
--   A Generalized Stein Lemma for Quantum Channels, arXiv:2609.30762v1, PDF p. 12, Proposition 8

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P69

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Information100.P69

attribute [local instance] Classical.propDecidable Classical.decEq

section Statements

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- Proposition 8, amplification along an unbounded sequence, then all lengths, PDF pp.12–13. -/
theorem amplification [Nonempty A] [Nonempty B] (N : Superop A B) (hN : IsChannel N) (F : BlockFamily A B)
    (omega : Matrix B B ℂ) (hconv : ConvexBlocks F) (htensor : TensorClosed F)
    (hreplacer : ReplacerWitness F omega) (r0 : ℝ) (hr0 : 0 ≤ r0)
    (k : ℕ → ℕ) (hk : ∀ j, 1 ≤ k j) (hkinf : Tendsto k atTop atTop)
    (L M : (j : ℕ) → Superop (Sites A (k j)) (Sites B (k j))) (lam : ℕ → ℝ)
    (hL : ∀ j, IsChannel (L j)) (hM : ∀ j, M j ∈ F (k j))
    (hlam : ∀ j, 1 ≤ lam j) (hdom : ∀ j, CPLe (L j) ((lam j:ℂ) • M j))
    (herr : Tendsto (fun j => diamond (L j-power N (k j))) atTop (nhds 0))
    (hrate : ∀ r : ℝ, r0 < r → ∀ᶠ j in atTop, Real.logb 2 (lam j) / k j ≤ r) :
    ∀ S : ℝ, r0 < S → ExponentialApproximation N F S := by sorry

end Statements

end QAlgorithms.Papers.Independent.Information100.P69

end
