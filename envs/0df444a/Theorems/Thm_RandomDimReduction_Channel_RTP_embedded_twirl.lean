-- Prove2me | Theorems.Thm_RandomDimReduction_Channel_RTP_embedded_twirl
-- name    : RandomDimReduction.Channel.RTP_embedded_twirl
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-17T18:02:13.213199+00:00
-- url     : https://prove2.me/theorems/4e1f4ce1-82ea-4de1-9559-9eb78583bf0e
-- title:
--   Exact reduction of an arbitrary embedded operator to its unitary twirl
-- statement:
--   Let $n,k,d$ be positive integers with $k\le d$, and let $R^{\mathrm{TP}}$ be the channel defined by the Grassmannian moment and kernel-completion term in Eq. (3). For every isometry $W:\mathbb C^k\to\mathbb C^d$ and every complex linear operator $X_0$ on $(\mathbb C^k)^{\otimes n}$,
--   $$R^{\mathrm{TP}}\big(W^{\otimes n}X_0(W^{\otimes n})^\dagger\big)=\mathbb E_{U\sim U(k)}\big[U^{\otimes n}X_0(U^{\otimes n})^\dagger\big].$$
--   No positivity or Hermiticity of $X_0$ is assumed. This is Eq. (1) of Theorem 1.1, the exact algebraic part of dimension reduction. It expresses independence from the unknown common embedding.
-- source:
--   Angus Lowe and Xinyu Tan, Random dimension reduction and learning symmetric properties of quantum states, STOC 2027 submission #994 (October 2026), Theorem 1.1 p.2; Section 2.3 pp.7–8, proof of Eq.(1). https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/994.pdf

import Definitions.Def_RandomDimReduction_Channel_Moment
import Definitions.Def_RandomDimReduction_Channel_Circuits

set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise ENNReal

namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

theorem RTP_embedded_twirl (n k d : ℕ) (hn : 0 < n) (hk : 1 ≤ k) (hkd : k ≤ d)
    (W : Matrix (Fin d) (Fin k) ℂ) (hW : Wᴴ * W = 1) (X₀ : Op (Word n k)) :
    RTP n k d (tensor n W * X₀ * (tensor n W)ᴴ) = twirl n k X₀ := by sorry

end RandomDimReduction.Channel
