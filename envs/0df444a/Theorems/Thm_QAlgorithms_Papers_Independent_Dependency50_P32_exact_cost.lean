-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P32_exact_cost
-- name    : QAlgorithms.Papers.Independent.Dependency50.P32.exact_cost
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:46:15.805914+00:00
-- url     : https://prove2.me/theorems/eab811d0-4fc1-48a9-88d4-8d69b85fc366
-- title:
--   Corollary 2: exact resource cost in both branches
-- statement:
--   All Hilbert spaces have strictly positive finite dimension. For each channel type, let $\mathcal O_{\rm all}$ be the closed convex physically allowed family of CPTP maps, with a nonempty closed convex free subset $\mathcal O$; primes indicate the output fibre. Let $\mathbb S$ be the maximal family of deterministic physical superchannels preserving both the allowed structures and the free fibres. Write $F$ for squared Uhlmann fidelity minimized over normalized reference-assisted input states, with an input-sized reference.
--
--   The multiplicative quantities $R_s$, $R_{\max}$, $R_H^\eta$, and $R_{\min}$ are standard robustness, generalized robustness, hypothesis-testing resource, and zero-error ordinary testing resource. Their affine versions use the affine saddle/equal-overlap domains; affine min-resource uses support-projector overlaps and is distinct from zero-error affine testing. Smoothing means the extended infimum over physically allowed channels with fidelity at least $1-\eta$; tolerances at least one give the whole allowed fibre. Unless specified otherwise, smoothing errors lie in $[0,1]$.
--
--   Let $\mathcal T$ be any physically allowed family of reference channels, possibly of different dimensions. Define $c^\epsilon_{\mathcal O}(E)$ as the infimum of $R_{\min,\mathcal O'}(T)$ over references $T$ admitting a free conversion $T\to E$ with fidelity at least $1-\epsilon$. Define $\lceil x\rceil_{\mathcal T}$ as the infimum of actually occurring reference values at least $x$. Then
--   $$
--   \begin{aligned}
--   [\forall T\in\mathcal T:\ R_{\min,\mathcal O'}(T)=R_{s,\mathcal O'}(T)]
--   &\Longrightarrow c^\epsilon_{\mathcal O}(E)=\lceil R_{s,\mathcal O}^\epsilon(E)\rceil_{\mathcal T},\\
--   [\forall T\in\mathcal T:\ R_{\min,\operatorname{aff}(\mathcal O')}(T)=R_{\max,\mathcal O'}(T)]
--   &\Longrightarrow c^\epsilon_{\mathcal O}(E)=\lceil R_{\max,\mathcal O}^\epsilon(E)\rceil_{\mathcal T}.
--   \end{aligned}
--   $$
--   These exact dilution formulas require no reference purity and do not assert a minimizing member of an arbitrary reference family.
-- source:
--   One-Shot Manipulation of Dynamical Quantum Resources, arXiv:2012.02215v3, PDF p. 3, Corollary 2: exact resource cost in both branches

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P32

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Dependency50.P32

open QAlgorithms.Papers.Independent.Information100.P07 (support)

/-- Corollary 2, PDF pp.3,12: both reference-collapse branches of resource
cost. The ceiling is over actually attainable reference VALUES; no reference
optimizer is asserted. The smooth input subscript is the input fibre O.
Source-scope correction: printed p.2 assumes only closed convex free fibres;
changed to the additional explicit ClosedConvexAllowed hypothesis, because
allowed-channel mixing and quantitative optimizer selection are used in the
conversion construction. The unrestricted allowed-subset case is not claimed. -/
theorem exact_cost (O : ResourceTheory) (hO : Regular O) (hAllowed : ClosedConvexAllowed O) (T : References)
    (hT : ValidReferences O T) {p : Port} (E : ChannelChoi p) (hE : E ∈ O.allowed p)
    (e : ℝ) (he : 0 ≤ e) (he1 : e ≤ 1) :
    ((∀ q, ∀ N ∈ T q, minimum O N = standard O N) →
      oneShotCost O T E e = referenceCeiling O T (smooth O (standard O) e E)) ∧
    ((∀ q, ∀ N ∈ T q, minimumAffine O N = maximal O N) →
      oneShotCost O T E e = referenceCeiling O T (smooth O (maximal O) e E)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P32

end
