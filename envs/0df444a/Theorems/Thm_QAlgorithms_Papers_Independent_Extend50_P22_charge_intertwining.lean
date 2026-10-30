-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P22_charge_intertwining
-- name    : QAlgorithms.Papers.Independent.Extend50.P22.charge_intertwining
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:26:23.263986+00:00
-- url     : https://prove2.me/theorems/f0d57c73-b79d-4db5-b780-53340f648706
-- title:
--   Unnumbered covariance/charge characterization, Eqs.(18)–(21)
-- statement:
--   Let $V:L\to A$ be an isometry between positive finite-dimensional Hilbert spaces, and let $T_L,T_A$ be Hermitian. The encoding channel $\mathcal E(X)=VXV^\dagger$ is covariant for every real parameter under $e^{-i\theta T_L}$ and $e^{-i\theta T_A}$ if and only if $$T_A V=V(T_L-\nu I_L)\quad\text{for some }\nu\in\mathbb R.$$ Equivalently, $T_A$ commutes with $VV^\dagger$ and $V^\dagger T_A V=T_L-\nu I_L$ for a single real offset. This is an isometric characterization, not a charge-conservation assertion for arbitrary covariant channels.
-- source:
--   Continuous symmetries and approximate quantum error correction, arXiv:1902.07714v1, PDF p. 7, Unnumbered covariance/charge characterization, Eqs.(18)–(21)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P22

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P22

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22 (bell)

open QAlgorithms.Papers.Independent.Support21.P09 (Irreducible)

open QAlgorithms.Papers.Independent.Renew46.P45 (symmetricWeight)

/-- PDF pp.7–8, (18)–(21): covariance iff a single scalar charge offset exists;
the compressed-charge/commutator condition is equivalent as well. -/
theorem charge_intertwining {d a : ℕ} (hd : 0 < d) (ha : 0 < a)
    (V : Matrix (Fin a) (Fin d) ℂ) (hV : Vᴴ * V = 1)
    (TL : Matrix (Fin d) (Fin d) ℂ) (TA : Matrix (Fin a) (Fin a) ℂ)
    (hL : TL.IsHermitian) (hA : TA.IsHermitian) :
    ((∀ theta : ℝ, ∀ X : Matrix (Fin d) (Fin d) ℂ,
      conjSuperop V (conjSuperop (chargeEvolution TL theta) X) =
        conjSuperop (chargeEvolution TA theta) (conjSuperop V X)) ↔
      ∃ nu : ℝ, TA * V = V * (TL - (nu : ℂ) • 1)) ∧
    ((∃ nu : ℝ, TA * V = V * (TL - (nu : ℂ) • 1)) ↔
      ∃ nu : ℝ, TA * (V * Vᴴ) = (V * Vᴴ) * TA ∧
        Vᴴ * TA * V = TL - (nu : ℂ) • 1) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P22

end
