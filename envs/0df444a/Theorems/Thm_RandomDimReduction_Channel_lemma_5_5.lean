-- Prove2me | Theorems.Thm_RandomDimReduction_Channel_lemma_5_5
-- name    : RandomDimReduction.Channel.lemma_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T11:25:05.466196+00:00
-- url     : https://prove2.me/theorems/5c507a13-28d7-4d36-ab40-6615f1cb16cf
-- title:
--   Lemma 5.5 — tensor powers of isometries in Schur coordinates
-- statement:
--   For positive $n,k,d$ with $k\le d$, let $W:\mathbb C^k\to\mathbb C^d$ satisfy $W^\dagger W=I$. Let $S_d,S_k$ be Schur transforms with the same labelled Specht model. There are maps $\eta_\lambda(W):V_\lambda^k\to V_\lambda^d$ with
--   $$ S_dW^{\otimes n}S_k^\dagger=\bigoplus_{\ell(\lambda)\le k}I_{\mathrm{Sp}_\lambda}\otimes\eta_\lambda(W),\qquad
--   \eta_\lambda(W)^\dagger\eta_\lambda(W)=I_{V_\lambda^k}. $$
--   The equality is rectangular and includes zero entries onto all absent output blocks. It preserves the isometry property in each Weyl block.
--
--   Differences from the source:
--   - encoding: finite-dimensional tensor Hilbert spaces and complex linear operators → matrices on Fin n → Fin d, with zero-based coordinates; reason: standard orthonormal coordinates preserve every operator and isometry
--   - reading: one Specht register is preserved between the d and k Schur transforms → one labelled unitary Specht model is shared across dimensions; reason: Algorithm 5.2 and Eq.(14) require compatible coordinates on this register
--   - encoding: direct sums over partitions whose height is at most the dimension → all partitions, with zero-dimensional absent Weyl factors; reason: empty factors contribute no coordinates or matrix entries
--   - generalization: the compatible Schur transforms chosen in §5.1 → every pair of Eq.(13) Schur transforms sharing any correctly labelled Specht model; reason: the source pair is one instance; a shared Specht model allows independent unitary changes of Weyl coordinates without changing the asserted identities
-- source:
--   Angus Lowe, Xinyu Tan, Random dimension reduction and learning symmetric properties of quantum states, STOC 2027 submission #994 (October 2026), Lemma 5.5, p.17. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/994.pdf

import Definitions.Def_RandomDimReduction_Channel_Schur

set_option autoImplicit false

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise ENNReal

namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma 5.5, p.17: the rectangular identity and every η†η = I.
Zero-dimensional absent blocks make the rectangular zero part explicit. -/
theorem lemma_5_5 (n k d : ℕ) (hn : 0 < n) (hk : 1 ≤ k) (hkd : k ≤ d)
    (κ : SpechtModel n) (Sd : SchurTransform κ d) (Sk : SchurTransform κ k)
    (W : Matrix (Fin d) (Fin k) ℂ) (hW : Wᴴ * W = 1) :
    ∃ eta : ∀ lam : Shape n, Matrix (Fin (weylDim d lam)) (Fin (weylDim k lam)) ℂ,
      Sd.U * tensor n W * Sk.Uᴴ =
        Matrix.blockDiagonal' (fun lam => Matrix.kronecker (1 : Op (Fin (spechtDim lam))) (eta lam)) ∧
      ∀ lam, (eta lam)ᴴ * eta lam = 1 := by sorry

end RandomDimReduction.Channel
