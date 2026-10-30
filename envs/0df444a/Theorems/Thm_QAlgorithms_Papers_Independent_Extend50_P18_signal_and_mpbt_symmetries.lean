-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P18_signal_and_mpbt_symmetries
-- name    : QAlgorithms.Papers.Independent.Extend50.P18.signal_and_mpbt_symmetries
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:01:03.199285+00:00
-- url     : https://prove2.me/theorems/47e75382-aeb3-4354-becb-54e4bdc394e1
-- title:
--   Unnumbered §§II,IV: exact signal and MPBT symmetries
-- statement:
--   Let $d\ge1$, $k\ge1$, and $N\ge2k$. Use the fixed Bell resource, ordered port choices $i$, signal states $\sigma_i$, their sum $\rho$, and completed square-root effects $\Pi_i$. For $\tau\in S_N$ let $V_\tau$ permute the port registers, and put $\tau i=\tau\circ i$. For $U\in U(d)$ put $W_U=U^{\otimes N}\otimes\overline U^{\otimes k}$. Then
--
--   $$
--   V_\tau\sigma_iV_\tau^\dagger=\sigma_{\tau i},\qquad
--   V_\tau\rho V_\tau^\dagger=\rho,\qquad
--   V_\tau\Pi_iV_\tau^\dagger=\Pi_{\tau i},
--   $$
--
--   and
--
--   $$
--   W_U\sigma_iW_U^\dagger=\sigma_i,\qquad W_U\rho W_U^\dagger=\rho.
--   $$
--
--   These are exact physical symmetries. The conjugation bar is entrywise complex conjugation, and the permutation action is the actual group action.
-- source:
--   Efficient multi port-based teleportation schemes, arXiv:2008.00984v4, PDF p. 7, Unnumbered §§II,IV

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P18

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P18

attribute [local instance] Classical.propDecidable

/-- All signal and MPBT symmetries of §IV, and the resulting SRM covariance:
actual permutation action, not an action of a quotient set (PDF pp.7-8,
(22)-(23)). Entrywise conjugation in mixedUnitary is essential. -/
theorem signal_and_mpbt_symmetries (d N k : ℕ) (hd : 0 < d)
    (hk : 0 < k) (hports : 2*k ≤ N) :
    (∀ (tau : Equiv.Perm (Fin N)) (i : PortChoice N k),
      portPermutation tau * mpbtSignal (d := d) i * (portPermutation tau)ᴴ =
        mpbtSignal (permuteChoice tau i)) ∧
    (∀ tau : Equiv.Perm (Fin N),
      portPermutation (d := d) (k := k) tau * mpbtOperator d N k * (portPermutation tau)ᴴ =
        mpbtOperator d N k) ∧
    (∀ (U : Matrix.unitaryGroup (Fin d) ℂ) (i : PortChoice N k),
      mixedTensorAction U * mpbtSignal (d := d) i * (mixedTensorAction U)ᴴ = mpbtSignal i) ∧
    (∀ U : Matrix.unitaryGroup (Fin d) ℂ,
      mixedTensorAction U * mpbtOperator d N k * (mixedTensorAction U)ᴴ = mpbtOperator d N k) ∧
    (∀ (tau : Equiv.Perm (Fin N)) (i : PortChoice N k),
      portPermutation tau * srmEffect (d := d) i * (portPermutation tau)ᴴ =
        srmEffect (permuteChoice tau i)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P18

end
