-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P29_finite_group_permutation_code
-- name    : QAlgorithms.Papers.Independent.Extend50.P29.finite_group_permutation_code
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:11:08.055662+00:00
-- url     : https://prove2.me/theorems/c417022b-c8d8-4519-8466-e6c0c2ba39cd
-- title:
--   Case 3: tensor-power permutation-covariant exact codes for every finite group
-- statement:
--   Let a finite group $G$ act on a finite set $A$. Let $\mathcal H_{\rm in}$ and $\mathcal H$ be nonzero finite-dimensional complex Hilbert spaces. Let $0\le k\le n$, and let $\mathcal E_0$ be any CPTP encoding from $\mathcal H_{\rm in}$ into $\mathcal H^{\otimes n}$ that corrects every known erased subset of at most $k$ modes, exactly on all input density matrices. Define the tensor-product channel on the entire input, including entangled states, by
--   $$\mathcal E=\bigotimes_{a\in A}\mathcal E_0:\ S(\mathcal H_{\rm in}^{\otimes A})\longrightarrow S\bigl((\mathcal H^{\otimes A})^{\otimes n}\bigr).$$
--   Let $P(g)$ permute the $A$ factors with coordinate rule $a\mapsto g^{-1}a$. Then $\mathcal E$ is CPTP and
--   $$\mathcal E(P_{\rm in}(g)\rho P_{\rm in}(g)^\dagger)=P_{\rm out}(g)\mathcal E(\rho)P_{\rm out}(g)^\dagger.$$
--   It also exactly corrects erasure of every subset of at most $k$ grouped physical shares. Taking $A=G$ gives the regular permutation construction for each finite group; no prescribed irreducible logical representation is asserted.
-- source:
--   Error Correction of Quantum Reference Frame Information, arXiv:1709.04471v1, PDF p. 4, Case 3: tensor-power permutation-covariant exact codes for every finite group

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P29

noncomputable section

open MeasureTheory MeasureTheory.Measure

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Extend50.P29

open QAlgorithms.Papers.Independent.Information100.P32 (evolution)

open QAlgorithms.Papers.Independent.Next46.P39 (inverseSqrt rectAct)

open QAlgorithms.Papers.Independent.Support21.P09 (groupLeftRegular)

/-- PDF pp.4--5, Case 3: the specified tensor-power channel is CPTP,
permutation-covariant and inherits every at-most-k share erasure correction.
Taking A=G with the regular action gives the finite-group construction. -/
theorem finite_group_permutation_code
    {G A I H : Type} [Group G] [Fintype G] [Fintype A] [MulAction G A]
    [Fintype I] [Nonempty I] [Fintype H] [Nonempty H]
    {n k : ℕ} (hkn : k ≤ n)
    (E0 : Superop I (Fin n → H)) (hE0 : IsChannel E0)
    (hcorrect : CorrectsErasedSubsets (H := fun _ : Fin n => H) k E0) :
    IsChannel (tensorEncoding (A := A) E0) ∧
    ErasureCovariant (H := fun _ : Fin n => A → H)
      (fun g : G => copyPermutation (A := A) (I := I) g)
      (fun (g : G) (_ : Fin n) => copyPermutation (A := A) (I := H) g) (tensorEncoding (A := A) E0) ∧
    CorrectsErasedSubsets (H := fun _ : Fin n => A → H) k (tensorEncoding (A := A) E0) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P29

end
