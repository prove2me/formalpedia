-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P06_supportDominatingState
-- name    : QAlgorithms.Papers.Independent.Claimed50.P06.supportDominatingState
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:06:22.072245+00:00
-- url     : https://prove2.me/theorems/e823ab59-fcd3-4c27-9939-8c0332a9fd2f
-- title:
--   A support-dominating state in a closed convex family
-- statement:
--   Let $\mathcal A$ be a sigma-finite von Neumann algebra in standard form on an arbitrary complex Hilbert space. Let $\mathcal S$ be a nonempty convex set of normal states, closed in the norm of linear functionals. There is a normal state $\sigma\in\mathcal S$ such that
--
--   $$\operatorname{supp}(\rho)\le\operatorname{supp}(\sigma)\qquad(\rho\in\mathcal S).$$
--
--   This selects one reference state whose support covers the entire family.
--
--   **Formalization Note** Normal states are bounded linear functionals admitting unit-vector representatives in the standard representation. Support containment is expressed equivalently by $\sigma(a^*a)=0\Rightarrow\rho(a^*a)=0$ for every $a\in\mathcal A$. The ambient dual norm restricts to the predual norm. Nonemptiness, implicit in the proof, is stated explicitly.
-- source:
--   Approximate recovery and relative entropy I. general von Neumann subalgebras, arXiv:2006.08002v1, PDF p. 8, Lemma 2: support-dominating state in a closed convex set

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P06

noncomputable section

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Claimed50.P06

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Lemma 2, PDF p.8; proof pp.32–33. A nonempty norm-closed convex set of
normal states on a sigma-finite von Neumann algebra contains a state whose
support contains every member's support. Nonemptiness is implicit in the proof
and necessary (the empty closed convex set otherwise contradicts the claim). -/
theorem supportDominatingState
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) (_form : StandardForm A)
    (hSigmaFinite : IsSigmaFinite A)
    (S : Set (A →L[ℂ] ℂ)) (hNonempty : S.Nonempty)
    (hClosed : IsClosed S) (hConvex : Convex ℝ S)
    (hStates : ∀ rho ∈ S, IsNormalState A rho) :
    ∃ sigma ∈ S, ∀ rho ∈ S, SupportContained A rho sigma := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P06

end
