-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P20_additivitySingleLetterizes
-- name    : QAlgorithms.Papers.Independent.Claimed50.P20.additivitySingleLetterizes
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:16:53.840481+00:00
-- url     : https://prove2.me/theorems/ec473173-089f-4bcf-b7ad-8513d292f3c3
-- title:
--   Lemma 1: additivity implies single-letterization
-- statement:
--   Let $\mathcal N:A'\to B$ be a completely positive trace-preserving map between nonzero finite-dimensional quantum registers. All entropies are in bits, with $0\log 0=0$. Every ensemble is finite, its weights are nonnegative and sum to one, and every component is normalized, including components of weight zero.
--
--   For any finite reference $A$ and pure input ensemble $\{p_x,\phi_x^{AA'}\}$, write $\sigma_x^{AB}=(\mathrm{id}_A\otimes\mathcal N)(\phi_x)$ and attach its classical label $X$. Set $J_\sigma=I(AX;B)_\sigma$, $K_\sigma=\sum_xp_x[H(B)_{\sigma_x}-H(AB)_{\sigma_x}]=I(A\rangle BX)_\sigma$, and $L_\sigma=I(X;B)_\sigma+K_\sigma$. The arbitrary reference dimension and the alphabet size are included in all ensemble optimizations. For finite weights $\lambda,\mu\ge0$, let $D_{\lambda,\mu}(\mathcal N)=\max_\sigma[J_\sigma+\lambda K_\sigma+\mu L_\sigma]$, where all three quantities use the same ensemble.
--
--   Fix $\lambda,\mu\ge0$ and assume global pairwise additivity: for every two channels $\mathcal F,\mathcal G$ on arbitrary nonzero finite registers, $D_{\lambda,\mu}(\mathcal F\otimes\mathcal G)=D_{\lambda,\mu}(\mathcal F)+D_{\lambda,\mu}(\mathcal G)$. Then
--
--   $$D_{\lambda,\mu}^{\mathrm{reg}}(\mathcal N)=D_{\lambda,\mu}(\mathcal N),\qquad \lim_{n\to\infty}\frac1nD_{\lambda,\mu}(\mathcal N^{\otimes n})=D_{\lambda,\mu}^{\mathrm{reg}}(\mathcal N).$$
--
--   Here the regularized value is implemented as the supremum of positive-block per-use values; the asserted convergence pins it to the source's genuine limit. This is single-letterization, with no hypothesis restricting the input to product states.
-- source:
--   The quantum dynamic capacity formula of a quantum channel, arXiv:1004.0458v3, PDF p. 12, Lemma 1: additivity implies single-letterization

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P20

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble PureEnsemble channelHolevo)

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

open QAlgorithms.Papers.Independent.Dependency50.P23 (IsHadamard)

open QAlgorithms.Papers.Independent.Dependency50.P41 (qubitErasure)

open QAlgorithms.Papers.Independent.Information100.P27 (qubitDephasing)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma 1, PDF p.12: global pairwise additivity gives both the genuine limit
and equality of its positive-block supremum implementation with the one-letter value. -/
theorem additivitySingleLetterizes
    {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B] (N : Superop A B) (hN : IsChannel N)
    (lambda mu : ℝ) (hlambda : 0 ≤ lambda) (hmu : 0 ≤ mu)
    (hadd : AdditiveDynamic lambda mu) :
    regularizedDynamic N lambda mu = dynamic N lambda mu ∧
      Tendsto (fun n : ℕ => dynamic (piSuperop (fun _ : Fin n => N)) lambda mu / (n : ℝ))
        atTop (nhds (regularizedDynamic N lambda mu)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P20

end
