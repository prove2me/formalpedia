-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P70_peripheral_projection_exists
-- name    : QAlgorithms.Papers.Independent.Intake100.P70.peripheral_projection_exists
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:55:57.815604+00:00
-- url     : https://prove2.me/theorems/eaead1f9-1942-49fb-9f6e-7f6726859f67
-- title:
--   Unnumbered: a CPTP spectral projection onto rotating points
-- statement:
--   Let $\mathcal E$ be a CPTP endomorphism on a finite-dimensional nonzero complex Hilbert space. Let $\operatorname{Rot}(\mathcal E)$ be the complex peripheral span. There exist a CPTP map $F$ and positive recurrence times $N_n$ such that
--
--   $$\|\mathcal E_R^{N_n}-I_R\|_{2\to2}<3^{-(n+1)},\quad F=\lim_{n\to\infty}\mathcal E^{(n+1)N_n},\quad F^2=F,\quad\operatorname{ran}F=\operatorname{Fix}(F)=\operatorname{Rot}(\mathcal E).$$
--
--   The exponent sequence is unbounded and positive; convergence is in finite-dimensional superoperator norm, equivalently pointwise on all operators. The full sequence of powers need not converge.
-- source:
--   Information preserving structures: A general framework for quantum zero-error information, arXiv:1006.1358v1, PDF p. 28, Unnumbered: a CPTP spectral projection onto rotating points

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

/-- PDF p.28: a CPTP spectral projection onto Rot(E), using positive times
m_n=(n+1)N_{3^(-(n+1))}. This corrects the misleading ordinary-limit notation
(B11),(B13); no convergence of the full sequence E^n is asserted. -/
theorem peripheral_projection_exists {I : Type*} [Fintype I]
    [DecidableEq I] [Nonempty I] (E : Superop I I) (hE : IsChannel E) :
    ∃ F : Superop I I, IsPeripheralProjection E F ∧
      ∃ N : ℕ → ℕ, (∀ n, 0 < N n ∧
        RotatingRecurrence E (N n) ((1 / 3 : ℝ) ^ (n + 1))) ∧
      ∀ X, Tendsto (fun n => (E^[(n + 1) * N n]) X) atTop (nhds (F X)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P70

end
