-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P29_infinitesimal_logical_action_trivial
-- name    : QAlgorithms.Papers.Independent.Extend50.P29.infinitesimal_logical_action_trivial
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:08:53.381987+00:00
-- url     : https://prove2.me/theorems/dacb01bb-84d8-45a4-94a9-0551fbe3a266
-- title:
--   Case 1 / abstract: finite-dimensional covariant erasure correction forces trivial infinitesimal logical action
-- statement:
--   Let $n\ge1$, let $\mathcal H_{\rm in}$ and all $\mathcal H_i$ be nonzero finite-dimensional complex Hilbert spaces, and let $\mathcal E$ be a fixed CPTP encoding into $\bigotimes_{i=1}^n\mathcal H_i$. Suppose fixed CPTP decoders $\mathcal D_j$ recover every input density matrix after erasure of the known site $j$. Let $T_{\rm in}$ and $T_i$ be Hermitian generators. Assume that for every real $t$ and every density matrix $\rho$,
--   $$\mathcal E(e^{-itT_{\rm in}}\rho e^{itT_{\rm in}})=\left(\bigotimes_i e^{-itT_i}\right)\mathcal E(\rho)\left(\bigotimes_i e^{itT_i}\right).$$
--   Then
--   $$T_{\rm in}=c I\quad\text{for some }c\in\mathbb R.$$
--   Thus each logical infinitesimal conjugation action is trivial; scalar phases and mixed encodings are included.
-- source:
--   Error Correction of Quantum Reference Frame Information, arXiv:1709.04471v1, PDF p. 3, Case 1 / abstract: finite-dimensional covariant erasure correction forces trivial infinitesimal logical action

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P29

noncomputable section

open MeasureTheory MeasureTheory.Measure

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Extend50.P29

open QAlgorithms.Papers.Independent.Information100.P32 (evolution)

open QAlgorithms.Papers.Independent.Next46.P39 (inverseSqrt rectAct)

open QAlgorithms.Papers.Independent.Support21.P09 (groupLeftRegular)

/-- PDF pp.3--4, Eq.(5), and p.6 note [22]: a mixed CPTP encoding correcting
every one-site erasure has scalar logical generator. Scalar phases are permitted. -/
theorem infinitesimal_logical_action_trivial
    {n : ℕ} (hn : 1 ≤ n) {I : Type} [Fintype I] [Nonempty I]
    {H : Fin n → Type} [∀ i, Fintype (H i)] [∀ i, Nonempty (H i)]
    (E : Superop I (RegisterConfig H)) (hE : IsChannel E)
    (D : Decoders (I := I) H) (hD : ∀ j, IsChannel (D j))
    (hcorrect : SingleCorrects E D)
    (Tin : Matrix I I ℂ) (hTin : Tin.IsHermitian)
    (Ti : (i : Fin n) → Matrix (H i) (H i) ℂ) (hTi : ∀ i, (Ti i).IsHermitian)
    (hcov : ∀ t ρ, IsDensityMatrix ρ →
      E (conjSuperop (evolution Tin t) ρ) =
        conjSuperop (localTensorMatrix (fun i => evolution (Ti i) t)) (E ρ)) :
    ∃ c : ℝ, Tin = (c : ℂ) • (1 : Matrix I I ℂ) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P29

end
