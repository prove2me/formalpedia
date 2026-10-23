-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P42_private_tensor_closure
-- name    : QAlgorithms.Papers.Independent.Gap48.P42.private_tensor_closure
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T05:38:26.130612+00:00
-- url     : https://prove2.me/theorems/837bff6f-18a8-4114-ad4d-3230395457b0
-- title:
--   Tensor powers retain the private-state structure with constructed data
-- statement:
--   Let $d,a,b$ be positive integers, let $\rho$ be a positive semidefinite trace-one shield state on $\mathbb C^a\otimes\mathbb C^b$, and let each $U_i$ be a unitary on that joint shield. Write
--
--   $$
--   \gamma^{(d)}=\frac1d\sum_{i,j=0}^{d-1}|ii\rangle\langle jj|\otimes U_i\rho U_j^\dagger,
--   $$
--
--   with the bipartition $AA':BB'$ and local shield dimensions $a,b$. All logarithms and resource rates are in bits.
--
--   For every positive integer $m$, use the same fixed bijection between key tuples $\mathbf i\in\{0,\ldots,d-1\}^m$ and labels in $\{0,\ldots,d^m-1\}$ on both owners. Construct $\rho_m=\rho^{\otimes m}$ and $V_{\mathbf i}=\bigotimes_{t=1}^m U_{i_t}$. Then $\rho_m$ is a density operator, each $V_{\mathbf i}$ is unitary, and after regrouping all key and shield registers within each owner,
--
--   $$
--   \operatorname{regroup}\bigl((\gamma^{(d)})^{\otimes m}\bigr)
--   =\frac1{d^m}\sum_{\mathbf i,\mathbf j}|\mathbf i\mathbf i\rangle\langle\mathbf j\mathbf j|\otimes V_{\mathbf i}\rho_mV_{\mathbf j}^{\dagger}.
--   $$
--
--   Thus the resulting state has private key dimension $d^m$ with the computed shield and twists. This structural identity supplies the tensor-power input to the cost bound.
-- source:
--   Quantum states representing perfectly secure bits are always distillable, arXiv:quant-ph/0602176v2, PDF p. 4, III, observation preceding Property 1a

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P42

namespace QAlgorithms.Papers.Independent.Gap48.P42

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.4, observation immediately before Property 1a: the actual regrouped
m-copy matrix is private with computed shield rho^tensor m and tensor twists.
The conclusion certifies normalization and both unitary identities of those
computed twists; no unrelated private target is existentially introduced. -/
theorem private_tensor_closure {d a b : ℕ}
    (hd : 0 < d) (ha : 0 < a) (hb : 0 < b)
    (rho : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hrho : IsDensityMatrix rho)
    (U : Fin d → Matrix.unitaryGroup (Fin a × Fin b) ℂ) (m : ℕ) (hm : 0 < m) :
    IsDensityMatrix (Dependency50.P42.dimensionedPower rho m) ∧
    (∀ key, (tensorTwists U m key)ᴴ * tensorTwists U m key = 1 ∧
      tensorTwists U m key * (tensorTwists U m key)ᴴ = 1) ∧
    (fun x y : Fin (d ^ m * a ^ m) × Fin (d ^ m * b ^ m) =>
      Dependency50.P42.dimensionedPower (bipartitePrivate rho U) m
        (regroupIndex d a m x.1, regroupIndex d b m x.2)
        (regroupIndex d a m y.1, regroupIndex d b m y.2)) =
      bipartitePrivateRaw (Dependency50.P42.dimensionedPower rho m) (tensorTwists U m) := by sorry

end

end QAlgorithms.Papers.Independent.Gap48.P42
