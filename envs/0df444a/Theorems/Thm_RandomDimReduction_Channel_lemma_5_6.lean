-- Prove2me | Theorems.Thm_RandomDimReduction_Channel_lemma_5_6
-- name    : RandomDimReduction.Channel.lemma_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T11:25:16.132225+00:00
-- url     : https://prove2.me/theorems/adc9a245-70ee-48c9-a088-7f640afed4ed
-- title:
--   Lemma 5.6 — moment, image and kernel projectors
-- statement:
--   For positive $n,k,d$ with $k\le d$, the Grassmannian moment is
--   $$ M_{k\hookrightarrow d}^{(n)}=\sum_{\ell(\lambda)\le k}\frac{\dim V_\lambda^k}{\dim V_\lambda^d}\Pi_\lambda. $$
--   Its orthogonal image projector equals $\Pi_{\le k}$, and its orthogonal kernel projector equals $\Pi_{>k}$. All three conclusions are included. The projectors are the actual isotypic projectors on the original tensor space, independently of a Schur coordinate choice.
--
--   Differences from the source:
--   - encoding: finite-dimensional tensor Hilbert spaces and complex linear operators → matrices on Fin n → Fin d, with zero-based coordinates; reason: standard orthonormal coordinates preserve every operator and isometry
--   - encoding: direct sums over partitions whose height is at most the dimension → all partitions, with zero-dimensional absent Weyl factors; reason: empty factors contribute no coordinates or matrix entries
-- source:
--   Angus Lowe, Xinyu Tan, Random dimension reduction and learning symmetric properties of quantum states, STOC 2027 submission #994 (October 2026), Lemma 5.6, p.17. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/994.pdf

import Definitions.Def_RandomDimReduction_Channel_Moment
import Definitions.Def_RandomDimReduction_Channel_Schur

set_option autoImplicit false

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise ENNReal

namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma 5.6, p.17: the moment formula, its image projector, and its kernel projector. -/
theorem lemma_5_6 (n k d : ℕ) (hn : 0 < n) (hk : 1 ≤ k) (hkd : k ≤ d) :
    moment n k d = (∑ lam : Shape n, if height lam ≤ k then
        ((weylDim k lam : ℂ) / (weylDim d lam : ℂ)) • isotypic d lam else 0) ∧
    imageProjector n k d = lowProjector n k d ∧
    kernelProjector n k d = highProjector n k d := by sorry

end RandomDimReduction.Channel
