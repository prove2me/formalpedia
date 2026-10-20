-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P32_exact_distillable
-- name    : QAlgorithms.Papers.Independent.Dependency50.P32.exact_distillable
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:47:39.540652+00:00
-- url     : https://prove2.me/theorems/4c458837-2738-45a6-a300-cd63e5c7214f
-- title:
--   Corollary 4: exact distillation in both branches
-- statement:
--   All Hilbert spaces have strictly positive finite dimension. For each channel type, let $\mathcal O_{\rm all}$ be the closed convex physically allowed family of CPTP maps, with a nonempty closed convex free subset $\mathcal O$; primes indicate the output fibre. Let $\mathbb S$ be the maximal family of deterministic physical superchannels preserving both the allowed structures and the free fibres. Write $F$ for squared Uhlmann fidelity minimized over normalized reference-assisted input states, with an input-sized reference.
--
--   The multiplicative quantities $R_s$, $R_{\max}$, $R_H^\eta$, and $R_{\min}$ are standard robustness, generalized robustness, hypothesis-testing resource, and zero-error ordinary testing resource. Their affine versions use the affine saddle/equal-overlap domains; affine min-resource uses support-projector overlaps and is distinct from zero-error affine testing. Smoothing means the extended infimum over physically allowed channels with fidelity at least $1-\eta$; tolerances at least one give the whole allowed fibre. Unless specified otherwise, smoothing errors lie in $[0,1]$.
--
--   Let every reference $T\in\mathcal T$ preserve purity on normalized reference-assisted pure inputs. Define $d^\epsilon_{\mathcal O}(E)$ as the supremum of the ordinary min-resource values of references obtainable from $E$ with fidelity at least $1-\epsilon$. Define $\lfloor x\rfloor_{\mathcal T}$ as the supremum of attainable reference values at most $x$. Then
--   $$
--   \begin{aligned}
--   [\forall T:\ R_{\min}(T)=R_s(T)]&\Longrightarrow d^\epsilon_{\mathcal O}(E)=\lfloor R_{H,\mathcal O}^\epsilon(E)\rfloor_{\mathcal T},\\
--   [\forall T:\ R_{\min,\operatorname{aff}}(T)=R_{\max}(T)]&\Longrightarrow d^\epsilon_{\mathcal O}(E)=\lfloor R_{H,\operatorname{aff}(\mathcal O)}^\epsilon(E)\rfloor_{\mathcal T}.
--   \end{aligned}
--   $$
--   Reference monotones are evaluated in their own target fibres. These formulas retain the operational reference scale and do not assume a maximizing reference exists.
-- source:
--   One-Shot Manipulation of Dynamical Quantum Resources, arXiv:2012.02215v3, PDF p. 3, Corollary 4: exact distillation in both branches

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P32

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Dependency50.P32

open QAlgorithms.Papers.Independent.Information100.P07 (support)

/-- Corollary 4, PDF pp.3,12: both exact distillation formulas, with pure
reference-assisted targets and a supremum over attainable reference values.
Source-scope correction: printed p.2 assumes only closed convex free fibres;
changed to the additional explicit ClosedConvexAllowed hypothesis, because
allowed-channel mixing and quantitative optimizer selection are used in the
conversion construction. The unrestricted allowed-subset case is not claimed. -/
theorem exact_distillable (O : ResourceTheory) (hO : Regular O) (hAllowed : ClosedConvexAllowed O) (T : References)
    (hT : ValidReferences O T) (hpure : ∀ q, ∀ N ∈ T q, PureTarget N)
    {p : Port} (E : ChannelChoi p) (hE : E ∈ O.allowed p)
    (e : ℝ) (he : 0 ≤ e) (he1 : e ≤ 1) :
    ((∀ q, ∀ N ∈ T q, minimum O N = standard O N) →
      oneShotDistillable O T E e = referenceFloor O T (testing O E e)) ∧
    ((∀ q, ∀ N ∈ T q, minimumAffine O N = maximal O N) →
      oneShotDistillable O T E e = referenceFloor O T (testingAffine O E e)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P32

end
