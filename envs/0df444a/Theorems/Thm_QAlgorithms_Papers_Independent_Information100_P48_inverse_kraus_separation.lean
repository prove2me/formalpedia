-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P48_inverse_kraus_separation
-- name    : QAlgorithms.Papers.Independent.Information100.P48.inverse_kraus_separation
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T11:43:28.870345+00:00
-- url     : https://prove2.me/theorems/f0a8a379-014a-424f-bfc3-8ac563476de8
-- title:
--   Forward/inverse control coherently separates ADC Kraus actions
-- statement:
--   Fix $\gamma\in[0,1]$ and the principal-angle ADC dilation $U$ on a system and one environmental qubit initially in $|0\rangle$. The inverse $U^\dagger$ and $(I\otimes Z)U$ agree on the clean-input subspace $S\otimes|0\rangle$. Both diagonal reductions realize the ADC; the two cross maps coincide and, on every operator $R$, equal
--
--   $$
--   \Gamma(R)=K_0RK_0^\dagger-K_1RK_1^\dagger.
--   $$
--
--   Preparing the control in $|+\rangle$ and coherently selecting forward/inverse evolution gives
--
--   $$
--   \Phi^D_+(R)=K_0RK_0^\dagger,\qquad \Phi^D_-(R)=K_1RK_1^\dagger.
--   $$
--
--   For a density input $\rho$, $p_+=1-\gamma\rho_{11}$ and $p_-=\gamma\rho_{11}$, and every strictly positive-probability output normalizes to a density matrix. This is Kraus-branch separation on one shared environment, with zero-probability branches kept unnormalized.
-- source:
--   Coherent Control of Channel Dilations Activate Temporal Bell Nonclassicality, arXiv:2607.05643v1, PDF p. 8, §III B, Eqs.(50)–(51): ADC forward/inverse control separates Kraus branches

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P48

namespace QAlgorithms.Papers.Independent.Information100.P48

open scoped Matrix ComplexConjugate

noncomputable section

/-- §III B, PDF p.8, Eqs.(50)–(51): forward/inverse control separates Kraus branches.
The inverse equals (I tensor Z)U on clean inputs only, not on all environmental inputs. -/
theorem inverse_kraus_separation (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) :
    (∀ (s t : Bool) (e : Bool),
      (dilation g)ᴴ (s, e) (t, false) =
        (Matrix.kronecker (1 : QOp) pauliZ * dilation g) (s, e) (t, false)) ∧
    (∀ rho : QOp,
      cross (dilation g)ᴴ (dilation g)ᴴ false rho = adc g rho ∧
      cross (dilation g) (dilation g)ᴴ false rho =
        k0 g * rho * (k0 g)ᴴ - k1 g * rho * (k1 g)ᴴ ∧
      cross (dilation g)ᴴ (dilation g) false rho =
        k0 g * rho * (k0 g)ᴴ - k1 g * rho * (k1 g)ᴴ ∧
      sharedADC g false rho = k0 g * rho * (k0 g)ᴴ ∧
      sharedADC g true rho = k1 g * rho * (k1 g)ᴴ) ∧
    (∀ rho : QOp, IsDensityMatrix rho → ∀ minus : Bool,
      (sharedADC g minus rho).trace.re =
        (if minus then g * (rho true true).re else 1 - g * (rho true true).re) ∧
      (0 < (sharedADC g minus rho).trace.re →
        IsDensityMatrix (normalize (sharedADC g minus rho)))) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P48
