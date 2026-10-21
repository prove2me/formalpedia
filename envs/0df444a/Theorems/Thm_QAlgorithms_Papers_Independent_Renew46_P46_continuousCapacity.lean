-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P46_continuousCapacity
-- name    : QAlgorithms.Papers.Independent.Renew46.P46.continuousCapacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:50:32.140869+00:00
-- url     : https://prove2.me/theorems/68ae296e-02c3-4569-99b0-7d45228964fa
-- title:
--   Proposition 3: constrained continuous-alphabet capacity, (15)
-- statement:
--   Let $A$ be an arbitrary Borel subset of a finite-dimensional Euclidean space, let $x\mapsto S_x$ be a weakly continuous family of normalized positive trace-class states on an arbitrary complex Hilbert space, and let the real cost $f$ extend continuously to the ambient space. Weak continuity means continuity of every matrix element. Let $E$ be a real budget with an affordable input. Define $C<\infty$ using countably supported input laws and discrete collective measurements. Let $\mathcal P_1$ contain all Borel probability laws with a defined finite integral $\int_A f\,d\pi\le E$, and put $\bar S_\pi=\int_AS_x\,\pi(dx)$. If $\sup_{\pi\in\mathcal P_1}H(\bar S_\pi)<\infty$, then
--
--   $$C=\sup_{\pi\in\mathcal P_1}\left[H(\bar S_\pi)-\int_AH(S_x)\,\pi(dx)\right].$$
--
--   The theorem includes singular and nondiscrete Borel input laws on the right. The proof's closure-cell minimizer issue is recorded without imposing a new closedness hypothesis.
-- source:
--   On Quantum Communication Channels with Constrained Inputs, arXiv:quant-ph/9705054v1, PDF p. 6, Proposition 3: constrained continuous-alphabet capacity, (15)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P46

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P46

open Filter MeasureTheory QAlgorithms.RealRegisters

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Proposition 3, PDF p.6, (15), assumptions pp.5-6. Arbitrary Borel alphabet,
all Borel probability laws on the RHS, countably supported priors on the
measured-capacity LHS. No closedness or approximation theorem is assumed.
The closure-cell minimizer in its proof need not lie in A; this proof gap is
recorded in MODERATION_NOTES without changing the theorem's hypotheses. -/
theorem continuousCapacity {I : Type} (d : ℕ)
    (A : Set (EuclideanSpace ℝ (Fin d))) (hA : MeasurableSet A)
    (S : A → constrainedCqState I) (hcontinuous : WeaklyContinuous (fun a => (S a).val))
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : Continuous f) (E : ℝ)
    (hfeasible : ∃ a : A, f a ≤ E)
    (hbound : MeasureEntropyBound (fun a => (S a).val) (fun a : A => f a.val) E)
    (hfinite : constrainedCqCapacity S (fun a : A => f a.val) E < ⊤) :
    constrainedCqCapacity S (fun a : A => f a.val) E =
      ⨆ pi : {pi : Measure A // MeasureAdmissible (fun a : A => f a.val) E pi},
        constrainedCqChi (fun a => (S a).val) pi.val := by sorry

end QAlgorithms.Papers.Independent.Renew46.P46

end
