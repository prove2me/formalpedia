-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P11_werner_covariance_block_simulation
-- name    : QAlgorithms.Papers.Independent.Support50.P11.werner_covariance_block_simulation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:11:59.48433+00:00
-- url     : https://prove2.me/theorems/d5125d34-45d8-452d-ac0f-9fc8308494e9
-- title:
--   §VII (62): generalized Werner–Holevo covariance and block simulation
-- statement:
--   For an integer $d\ge2$ and $0\le\alpha\le1$, define
--   $$\mathcal W^{(d,\alpha)}(X)=\frac{1-\alpha}{d+1}\bigl(\operatorname{Tr}(X)I+X^T\bigr)+\frac\alpha{d-1}\bigl(\operatorname{Tr}(X)I-X^T\bigr).$$
--   This is CPTP and, for every unitary $U$ and every operator $X$,
--   $$\mathcal W^{(d,\alpha)}(UXU^\dagger)=\overline U\mathcal W^{(d,\alpha)}(X)U^T.$$
--   For each $n\ge1$, the parallel block $\mathcal W^{\otimes n}$ has an exact local simulation with forward classical communication using its normalized Choi state, equivalently $n$ single-use Choi states. For every $K\ge1$,
--   $$F^{\mathrm{PPTp}}(\mathcal W^{\otimes n},K)=F_\Gamma(\nu_{\mathcal W^{\otimes n}},K).$$
--   The output conjugation corrects the printed order in (62) using the channel's defining formula; both endpoints of $\alpha$ are included.
-- source:
--   On the power of PPT-preserving and non-signalling codes, arXiv:1406.7142v2, PDF p. 10, §VII (62): generalized Werner–Holevo covariance and block simulation

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P11

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Support50.P11

open QAlgorithms.Papers.Independent.Information100.P34 (choi dephasing permutationMatrix)

open QAlgorithms.Papers.Independent.Information100.P21 (pt)

open QAlgorithms.Papers.Independent.Dependency50.P09 (tensorAction)

open QAlgorithms.Papers.Independent.Information100.P76 (swapMatrix)

open QAlgorithms.Papers.Independent.Information100.P69 (replacer)

open QAlgorithms.Papers.Independent.Gap20.P19 (wernerIsometry)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF pp.10--11, (62): the output conjugation is by entrywise conjugate U.
Printed U^T X conjugate(U) is corrected using (58)--(59). All parallel blocks admit
exact Choi simulation and have exactly the PPT distillation performance. -/
theorem werner_covariance_block_simulation
    (d : ℕ) (hd : 2 ≤ d) (alpha : ℝ) (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1) :
    IsChannel (wernerHolevoChannel d alpha) ∧
    (∀ U : Matrix.unitaryGroup (Fin d) ℂ, ∀ X,
      wernerHolevoChannel d alpha (conjSuperop (U : Matrix (Fin d) (Fin d) ℂ) X) =
        conjSuperop (fun i j => conj ((U : Matrix (Fin d) (Fin d) ℂ) i j))
          (wernerHolevoChannel d alpha X)) ∧
    (∀ n : ℕ, 0 < n →
      HasChoiSimulation (piSuperop (fun _ : Fin n => wernerHolevoChannel d alpha)) ∧
      ∀ K : ℕ, 0 < K →
        optimalCodeFidelity .PPTp (piSuperop (fun _ : Fin n => wernerHolevoChannel d alpha)) K =
          distillFidelity (choiState (piSuperop (fun _ : Fin n => wernerHolevoChannel d alpha))) K) := by sorry

end QAlgorithms.Papers.Independent.Support50.P11

end
