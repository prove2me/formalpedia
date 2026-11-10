-- Prove2me | Theorems.Thm_RandomDimReduction_Channel_lemma_5_4
-- name    : RandomDimReduction.Channel.lemma_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T11:24:52.323311+00:00
-- url     : https://prove2.me/theorems/1075fe33-5e91-41bf-b293-db1ffc02f774
-- title:
--   Lemma 5.4 — the unitary twirl in Schur coordinates
-- statement:
--   Let $n,d$ be positive, let $S_d$ be a Schur transform as in Eq.(13), and let $X$ be any complex operator on $(\mathbb C^d)^{\otimes n}$. Write $X_{\lambda\mu}$ for the blocks of $S_dXS_d^\dagger$. Then
--   $$ S_d\mathbb E_{U\in U(d)}[U^{\otimes n}X(U^{\otimes n})^\dagger]S_d^\dagger
--   =\bigoplus_{\ell(\lambda)\le d}\operatorname{tr}_{V_\lambda^d}(X_{\lambda\lambda})\otimes\frac{I_{V_\lambda^d}}{\dim V_\lambda^d}. $$
--   This is the whole-operator twirl, not a twirl of a channel or only of tensor-power states.
--
--   Differences from the source:
--   - encoding: finite-dimensional tensor Hilbert spaces and complex linear operators → matrices on Fin n → Fin d, with zero-based coordinates; reason: standard orthonormal coordinates preserve every operator and isometry
--   - encoding: direct sums over partitions whose height is at most the dimension → all partitions, with zero-dimensional absent Weyl factors; reason: empty factors contribute no coordinates or matrix entries
--   - generalization: the Schur transform chosen in §5.1 → every correctly labelled unitary Schur coordinate system satisfying Eq.(13); reason: the source transform is one instance; changing the Specht model and Weyl bases preserves the twirl identity
-- source:
--   Angus Lowe, Xinyu Tan, Random dimension reduction and learning symmetric properties of quantum states, STOC 2027 submission #994 (October 2026), Lemma 5.4, p.16. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/994.pdf

import Definitions.Def_RandomDimReduction_Channel_Schur

set_option autoImplicit false

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise ENNReal

namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma 5.4, p.16: the full n-fold twirl on every complex operator. -/
theorem lemma_5_4 (n d : ℕ) (hn : 0 < n) (hd : 1 ≤ d)
    (κ : SpechtModel n) (S : SchurTransform κ d) (X : Op (Word n d)) :
    S.U * twirl n d X * S.Uᴴ = twirlBlocks S X := by sorry

end RandomDimReduction.Channel
