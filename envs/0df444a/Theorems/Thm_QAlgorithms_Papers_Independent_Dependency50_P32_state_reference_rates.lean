-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P32_state_reference_rates
-- name    : QAlgorithms.Papers.Independent.Dependency50.P32.state_reference_rates
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:01:41.909935+00:00
-- url     : https://prove2.me/theorems/9d0feca9-003c-4f50-845a-7c2c8669059e
-- title:
--   Exact channel rates with pure-state references
-- statement:
--   Let a regular channel resource theory have an underlying state theory with free density sets $\mathcal F_d$, and suppose its trivial-input free preparations are exactly preparations of free states. Let $\mathcal T$ consist of preparations of chosen unit vectors $\phi$ in positive finite dimensions. Use ordinary channel min-resource as the reference scale, and the supremum/infimum reference floor and ceiling of (C3). For any allowed channel $E$ and $0\le\epsilon\le1$,
--   $$
--   \begin{aligned}
--   [\forall\phi:\ R_{s,\mathcal F}(\phi)=R_{\min,\mathcal F}(\phi)]
--   &\Longrightarrow\begin{cases}
--   c^\epsilon(E)=\lceil R_{s,\mathcal O}^\epsilon(E)\rceil_{\mathcal T},\\
--   d^\epsilon(E)=\lfloor R_{H,\mathcal O}^\epsilon(E)\rfloor_{\mathcal T},
--   \end{cases}\\
--   [\forall\phi:\ R_{\max,\mathcal F}(\phi)=R_{\min,\operatorname{aff}(\mathcal F)}(\phi)]
--   &\Longrightarrow\begin{cases}
--   c^\epsilon(E)=\lceil R_{\max,\mathcal O}^\epsilon(E)\rceil_{\mathcal T},\\
--   d^\epsilon(E)=\lfloor R_{H,\operatorname{aff}(\mathcal O)}^\epsilon(E)\rfloor_{\mathcal T}.
--   \end{cases}
--   \end{aligned}
--   $$
--   Here each vector denotes its pure density operator when used in a state measure. Cost and distillation optimize free physical deterministic conversions in opposite directions, with squared worst-case reference-assisted fidelity.
--
--   This substitutes state monotones only for the reference preparations. The arbitrary channel input retains channel resource measures, and no golden-state existence theorem is asserted.
-- source:
--   One-Shot Manipulation of Dynamical Quantum Resources, arXiv:2012.02215v3, PDF p. 14, Exact channel rates with pure-state references

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P32

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Dependency50.P32

open QAlgorithms.Papers.Independent.Information100.P07 (support)

/-- State-reference consequence, PDF p.14: both branches of BOTH cost and
distillation corollaries. Only reference preparations reduce to state measures;
the monotones of the arbitrary input CHANNEL remain channel monotones.
Source-scope correction: printed p.2 assumes only closed convex free fibres;
changed to the additional explicit ClosedConvexAllowed hypothesis, because
allowed-channel mixing and quantitative optimizer selection are used in the
conversion construction. The unrestricted allowed-subset case is not claimed. -/
theorem state_reference_rates (O : ResourceTheory) (hO : Regular O) (hAllowed : ClosedConvexAllowed O)
    (F : ∀ d : ℕ+, Set (Matrix (Fin d) (Fin d) ℂ)) (hF : PreparationTheory O F)
    (T : ∀ d : ℕ+, Set (EuclideanSpace ℂ (Fin d))) (hnorm : ∀ d, ∀ v ∈ T d, ‖v‖ = 1)
    {p : Port} (E : ChannelChoi p) (hE : E ∈ O.allowed p)
    (e : ℝ) (he : 0 ≤ e) (he1 : e ≤ 1) :
    let refs := stateReferences T
    ((∀ d, ∀ v ∈ T d, stateStandard (F d) (pureDensity v) = stateMinimum (F d) (pureDensity v)) →
      oneShotCost O refs E e = referenceCeiling O refs (smooth O (standard O) e E) ∧
      oneShotDistillable O refs E e = referenceFloor O refs (testing O E e)) ∧
    ((∀ d, ∀ v ∈ T d, stateMaximal (F d) (pureDensity v) = stateMinimumAffine (F d) (pureDensity v)) →
      oneShotCost O refs E e = referenceCeiling O refs (smooth O (maximal O) e E) ∧
      oneShotDistillable O refs E e = referenceFloor O refs (testingAffine O E e)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P32

end
