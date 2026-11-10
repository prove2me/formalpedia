-- Prove2me | Theorems.Thm_RandomDimReduction_Channel_lemma_2_2
-- name    : RandomDimReduction.Channel.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T11:24:59.302993+00:00
-- url     : https://prove2.me/theorems/ae3b2952-17da-4ebc-b0aa-ceadf18b67d9
-- title:
--   Lemma 2.2 — the kernel annihilates embedded operators
-- statement:
--   Let $n,k,d$ be positive integers with $k\le d$, $W:\mathbb C^k\to\mathbb C^d$ an isometry, and $X_0$ any complex operator on the $n$-copy input. Put $X=W^{\otimes n}X_0(W^{\otimes n})^\dagger$ and let $Q$ be the projector onto the kernel of the moment $M$. Then
--   $$ QX=0\quad\text{and}\quad XQ=0. $$
--   Both identities hold without positivity or Hermiticity of $X_0$. They identify the support needed by the moment normalization.
--
--   Differences from the source:
--   - encoding: finite-dimensional tensor Hilbert spaces and complex linear operators → matrices on Fin n → Fin d, with zero-based coordinates; reason: standard orthonormal coordinates preserve every operator and isometry
--   - encoding: an operator X with hypothesis X = W tensor X₀ tensor W† → the embedded expression is substituted directly for X; reason: substitution preserves every instance of the source equality hypothesis
-- source:
--   Angus Lowe, Xinyu Tan, Random dimension reduction and learning symmetric properties of quantum states, STOC 2027 submission #994 (October 2026), Lemma 2.2, p.7. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/994.pdf

import Definitions.Def_RandomDimReduction_Channel_Moment

set_option autoImplicit false

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise ENNReal

namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma 2.2, p.7: both annihilation identities, for arbitrary complex X₀. -/
theorem lemma_2_2 (n k d : ℕ) (hn : 0 < n) (hk : 1 ≤ k) (hkd : k ≤ d)
    (W : Matrix (Fin d) (Fin k) ℂ) (hW : Wᴴ * W = 1) (X₀ : Op (Word n k)) :
    let X := tensor n W * X₀ * (tensor n W)ᴴ
    kernelProjector n k d * X = 0 ∧ X * kernelProjector n k d = 0 := by sorry

end RandomDimReduction.Channel
