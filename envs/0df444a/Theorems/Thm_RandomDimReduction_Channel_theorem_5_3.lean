-- Prove2me | Theorems.Thm_RandomDimReduction_Channel_theorem_5_3
-- name    : RandomDimReduction.Channel.theorem_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T11:25:46.911428+00:00
-- url     : https://prove2.me/theorems/3247f84c-909d-4ee3-a48e-9a0d8af756f7
-- title:
--   Theorem 5.3 — Algorithm 5.2 implements the reduction
-- statement:
--   For positive $n,k,d$ with $k\le d$, use compatible exact Schur transforms $S_d,S_k$. The map constructed from the steps of Algorithm 5.2 equals the integral-defined $R^{\rm TP}$ on every complex operator $X$. Moreover,
--   $$ S_kR^{\rm TP}(X)S_k^\dagger=\operatorname{tr}(\Pi_{>k}X)\frac{I}{k^n}
--   +\bigoplus_{\ell(\lambda)\le k}\operatorname{tr}_{V_\lambda^d}(X_{\lambda\lambda})\otimes\frac{I_{V_\lambda^k}}{\dim V_\lambda^k}. $$
--   Both the operational equality and the displayed identity are required. The result applies to all operators, including those outside the promised low-dimensional input support.
--
--   Differences from the source:
--   - encoding: finite-dimensional tensor Hilbert spaces and complex linear operators → matrices on Fin n → Fin d, with zero-based coordinates; reason: standard orthonormal coordinates preserve every operator and isometry
--   - reading: one Specht register is preserved between the d and k Schur transforms → one labelled unitary Specht model is shared across dimensions; reason: Algorithm 5.2 and Eq.(14) require compatible coordinates on this register
--   - encoding: direct sums over partitions whose height is at most the dimension → all partitions, with zero-dimensional absent Weyl factors; reason: empty factors contribute no coordinates or matrix entries
--   - encoding: the Moore–Penrose inverse followed by its positive square root → real spectral functional calculus x ↦ (sqrt x)⁻¹, with zero at zero; reason: the Grassmannian moment is positive semidefinite; its finite spectrum includes zero and needs no invertibility hypothesis
--   - generalization: the compatible Schur transforms chosen in §5.1 → every pair of Eq.(13) Schur transforms sharing any correctly labelled Specht model; reason: the source pair is one instance; a shared Specht model allows independent unitary changes of Weyl coordinates without changing the asserted identities
-- source:
--   Angus Lowe, Xinyu Tan, Random dimension reduction and learning symmetric properties of quantum states, STOC 2027 submission #994 (October 2026), Theorem 5.3, p.16. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/994.pdf

import Definitions.Def_RandomDimReduction_Channel_Moment
import Definitions.Def_RandomDimReduction_Channel_Algorithm

set_option autoImplicit false

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise ENNReal

namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Theorem 5.3, p.16: algorithm equality AND the displayed identity, on all operators. -/
theorem theorem_5_3 (n k d : ℕ) (hn : 0 < n) (hk : 1 ≤ k) (hkd : k ≤ d)
    (κ : SpechtModel n) (Sd : SchurTransform κ d) (Sk : SchurTransform κ k) :
    (∀ X : Op (Word n d), algorithm52 Sd Sk X = RTP n k d X) ∧
    (∀ X : Op (Word n d), Sk.U * RTP n k d X * Sk.Uᴴ =
      (((highProjector n k d * X).trace) / (k ^ n : ℕ)) • 1 +
        reductionBlocks (k := k) Sd X) := by sorry

end RandomDimReduction.Channel
