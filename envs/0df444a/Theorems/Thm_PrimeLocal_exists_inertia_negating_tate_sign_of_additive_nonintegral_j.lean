-- Prove2me | Theorems.Thm_PrimeLocal_exists_inertia_negating_tate_sign_of_additive_nonintegral_j
-- name    : PrimeLocal.exists_inertia_negating_tate_sign_of_additive_nonintegral_j
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-15T00:15:38.776957+00:00
-- url     : https://prove2.me/theorems/115ea275-8269-4104-bd38-671d72b06831
-- title:
--   Additive reduction with non-integral j: inertia moves the Tate sign
-- statement:
--   Given Tate sign data (qT, d, s, C) for a curve minimal at q with additive reduction (q divides the discriminant and c4) and non-integral j, some inertia element of Gal(Qbar_q/Q_q) moves the square root s, i.e. the Tate twist is ramified.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_FreyPackage_frey_no_cofixed_large.lean

import Mathlib
import Definitions.Def_EllipticCurve_ZeroComponentAt
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_FLTPrelim_CofixedLine
import Definitions.Def_TateCurve_TateParameter

set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open scoped WeierstrassCurve.Affine NNReal

namespace PrimeLocal
theorem exists_inertia_negating_tate_sign_of_additive_nonintegral_j (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) (q : ℕ) [Fact q.Prime] (hj : ¬ ((q : ℤ) ^ padicValInt q W.Δ ∣ W.c₄ ^ 3)) (qT : ℚ_[q]) (_ : qT ≠ 0) (_ : ‖qT‖₊ < 1) (d : ℚ_[q]) (s : AlgebraicClosure ℚ_[q]) (C : WeierstrassCurve.VariableChange (AlgebraicClosure ℚ_[q])) (hs : s ^ 2 = algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q]) d) (hC : C • ((W.map (Int.castRingHom ℚ_[q])).map (algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q]))) = (TateCurve.curve qT).map (algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q]))) (hCσ : ∀ σ : AlgebraicClosure ℚ_[q] ≃ₐ[ℚ_[q]] AlgebraicClosure ℚ_[q], (σ s = s → C.map σ.toAlgHom.toRingHom = C) ∧ (σ s ≠ s → C.map σ.toAlgHom.toRingHom = ⟨-1, 0, -1, 0⟩ * C)) (hmin : WeierstrassCurve.IsMinimal ℤ_[q] (W.map (Int.castRingHom ℚ_[q]))) (hqΔ : (q : ℤ) ∣ W.Δ) (hqc₄ : (q : ℤ) ∣ W.c₄) : ∃ σ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q, (∀ x : PadicAlgCl q, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1) ∧ σ s ≠ s := by sorry
end PrimeLocal
