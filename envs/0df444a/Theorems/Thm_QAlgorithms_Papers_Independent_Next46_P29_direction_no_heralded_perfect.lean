-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P29_direction_no_heralded_perfect
-- name    : QAlgorithms.Papers.Independent.Next46.P29.direction_no_heralded_perfect
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:27:08.935411+00:00
-- url     : https://prove2.me/theorems/52a63e25-00bf-49e8-9ec8-632539179ecd
-- title:
--   No nonzero universal heralded recovery of a dephased direction message
-- statement:
--   Let $k=2j_R\ge0$, and let $\mathcal E_k$ be the actual SU(2) Haar encoding using the highest-weight spin-$j_R$ token and spin-$1/2$ message. Let $\Delta$ denote z-basis dephasing. Consider any completely positive trace-nonincreasing accepted operation $\mathcal F$ on the joint register. If for every qubit density operator $\rho$ there is a possibly input-dependent probability $p_\rho\in[0,1]$ with $\mathcal F\mathcal E_k(\rho)=p_\rho\Delta(\rho)$, then
--
--   $$\mathcal F\mathcal E_k(\rho)=0\qquad\text{for every density operator }\rho.$$
--
--   Thus no nonzero universal accepted branch perfectly recovers an arbitrary dephased message. This does not prohibit a branch that heralds one distinguished known state.
-- source:
--   Quantum communication using a bounded-size quantum reference frame, arXiv:0812.5040v2, PDF p. 16, §VI.B: no heralded perfect recovery of the dephased qubit

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P29

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder Manifold ContDiff Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Next46.P29

open QAlgorithms.Papers.Independent.Information100.P56 (IsIrreducible)

open QAlgorithms.Papers.Independent.Information100.P63 (mixed)

open QAlgorithms.Papers.Independent.Information100.P34 (dephasing)

open QAlgorithms.Papers.Independent.Information100.P71 (IsSubchannel)

attribute [local instance] Classical.decEq Classical.propDecidable

/-- PDF p.16, final paragraph: no nonzero accepted CP trace-nonincreasing
branch can recover every dephased input. Success is allowed to depend on the input;
recovering one distinguished known state is not the universally quantified task. -/
theorem direction_no_heralded_perfect (k : ℕ)
    (F : Superop (Fin (k + 1) × Fin 2) (Fin 2)) (hF : IsSubchannel F)
    (hExact : ∀ rho, IsDensityMatrix rho → ∃ p : ℝ,
      0 ≤ p ∧ p ≤ 1 ∧ F (directionEncoding k rho) = (p : ℂ) • dephasing rho) :
    ∀ rho, IsDensityMatrix rho → F (directionEncoding k rho) = 0 := by sorry

end QAlgorithms.Papers.Independent.Next46.P29

end
