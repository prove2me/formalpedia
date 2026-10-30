-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P15_reference_fidelity_overlap
-- name    : QAlgorithms.Papers.Independent.Extend50.P15.reference_fidelity_overlap
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:54:32.649236+00:00
-- url     : https://prove2.me/theorems/a5628fd5-86b1-4cd4-bdd6-20608f3f31fd
-- title:
--   Reference-frame fidelity from interior weight overlaps
-- statement:
--   Let $d\ge2$, let $n_C\ge0$, and put $n'=n_C+d-1$. After an erasure syndrome, suppose a nonempty surviving reference has the form (A9), with $m\ge1$ rotated qudits and its actual probability weights $q_\lambda$ on size-$m$ Young diagrams of height at most $d$. Let $p(U\mid I)=|\sum_\lambda\sqrt{q_\lambda}\chi_{U^{-1},\lambda}|^2$ be the canonical covariant estimate density with respect to normalized Haar measure on $\mathrm{SU}(d)$. Write $\mathcal U_C$ for conjugation by $U^{\otimes n_C}$ and $\mathcal U_L^*$ for conjugation by entrywise complex conjugation of $U$.
--
--   Let $S_{\mathrm{int}}$ be the positive support of $q$ whose distinct row lengths have gaps greater than $3n'$, and let $S_{\mathrm{diff}}=\{\Delta\in\mathbb Z^d:|\Delta_i|\le n',\ \sum_i\Delta_i=0\}$. Extend $q$ by zero outside its Young diagrams. Then
--
--   $$F_{\mathrm{wc}}\!\left(\int p(U\mid I)\,\mathcal U_C\otimes\mathcal U_L^*\,dU,\mathcal I_C\otimes\mathcal I_L\right)\ge\min_{\Delta\in S_{\mathrm{diff}}}\sum_{\lambda\in S_{\mathrm{int}}}\sqrt{q_\lambda q_{\lambda+\Delta}}.$$
--
--   Here $F_{\mathrm{wc}}$ is stabilized squared Uhlmann fidelity. The finite minimum exists because $S_{\mathrm{diff}}$ contains zero; an empty interior gives a zero lower bound. This estimate isolates the surviving reference frame's contribution to recovery fidelity.
-- source:
--   Optimal Universal Quantum Error Correction via Bounded Reference Frames, arXiv:2007.09154v2, PDF p. 15, Lemma 2, A38--A39

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P15

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Extend50.P15

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity)

open QAlgorithms.Papers.Independent.Information100.P56 (normalizedChoi)

open QAlgorithms.Papers.Independent.Information100.P75 (Register)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Lemma 2, A39, PDF pp.15--17. Here m is the positive number of rotated qudits
in the surviving reference, with its actual syndrome-dependent law q. It asserts
nothing about an all-erased reference. The statement is independent of the invalid
arbitrary-channel assertion in Lemma 3. -/
theorem reference_fidelity_overlap (d m nC : ℕ) (hd : 2 ≤ d) (hm : 1 ≤ m)
    (mu : Measure (Matrix.specialUnitaryGroup (Fin d) ℂ)) (hmu : IsNormalizedHaar mu)
    (L : Finset (QAlgorithms.Schur.Partition d m))
    (q : QAlgorithms.Schur.Partition d m → ℝ)
    (hq : ∀ lambda ∈ L, 0 ≤ q lambda) (hqsum : ∑ lambda ∈ L, q lambda = 1) :
    minimumInteriorOverlap (nC + d - 1) L q ≤
      worstFidelity (referenceCostChannel mu nC L q) id := by sorry

end QAlgorithms.Papers.Independent.Extend50.P15

end
