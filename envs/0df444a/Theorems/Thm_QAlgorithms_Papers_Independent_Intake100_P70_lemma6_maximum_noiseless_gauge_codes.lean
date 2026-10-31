-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P70_lemma6_maximum_noiseless_gauge_codes
-- name    : QAlgorithms.Papers.Independent.Intake100.P70.lemma6_maximum_noiseless_gauge_codes
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:37:09.513818+00:00
-- url     : https://prove2.me/theorems/285f60a1-37db-4ff4-a6de-f73b8e4037da
-- title:
--   Lemma 6: full-rank channels classify maximum noiseless codes
-- statement:
--   Let $\mathcal E$ be a CPTP endomorphism on a finite-dimensional nonzero complex Hilbert space. Maximum means that no code satisfying the same criterion has a proper subset 1-isometric to $C$. Assume a positive full-rank fixed operator exists, and fix any canonical decomposition $H=\bigoplus_k(A_k\otimes B_k)$ of the computed restricted-adjoint fixed algebra. A convex density code $C$ is maximum noiseless if and only if there are density matrices $\tau_k$ on $B_k$, independent of the logical state, such that
--
--   $$C=\left\{\bigoplus_kp_k\rho_k\otimes\tau_k:p_k\ge0,\ \sum_kp_k=1,\ \rho_k\text{ arbitrary density matrices on }A_k\right\}.$$
--
--   The gauge states need not be fixed by the channel. Trace preservation is the standing channel assumption used in the proof.
-- source:
--   Information preserving structures: A general framework for quantum zero-error information, arXiv:1006.1358v1, PDF p. 9, Lemma 6: full-rank channels classify maximum noiseless codes

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P70

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Intake100.P70

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P21 (channelAdjoint)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart negativePart)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P34 (supportProjector)

/-- PDF pp.9–10,25, Lemma 6. CP in the headline is read with the standing
channel/TP assumption used in the proof. Full rank is a positive fixed operator.
Gauge states are independent of logical input; they need not be fixed by E. -/
theorem lemma6_maximum_noiseless_gauge_codes {I : Type*} [Fintype I]
    [DecidableEq I] [Nonempty I] (E : Superop I I) (hE : IsChannel E)
    (hFaithful : ∃ rho : Op I, rho.PosSemidef ∧ E rho = rho ∧ FullRankOn 1 rho)
    (B : BlockModel I) (hB : IsFixedDecomposition E B)
    (C : Set (Op I)) (hC : IsCode C) :
    MaximumCode (Noiseless E) C ↔
      ∃ tau : (k : Fin B.sectors) → Op (Fin (B.gaugeDim k)),
        (∀ k, IsDensityMatrix (tau k)) ∧ C = B.gaugeCode tau := by sorry

end QAlgorithms.Papers.Independent.Intake100.P70

end
