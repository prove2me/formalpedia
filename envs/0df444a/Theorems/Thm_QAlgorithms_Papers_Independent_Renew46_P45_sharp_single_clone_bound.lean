-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P45_sharp_single_clone_bound
-- name    : QAlgorithms.Papers.Independent.Renew46.P45.sharp_single_clone_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:40:42.60985+00:00
-- url     : https://prove2.me/theorems/515d9648-2f24-422d-b262-5aad3b5edf6f
-- title:
--   Sharp single-clone error bound and explicit attainment
-- statement:
--   Let $d\ge1$, $N\ge1$ and $M>N$ be integers, and let $H=\mathbb C^d$. A cloning map is a complex-linear completely positive unital Heisenberg map $T:B(H^{\otimes M})\to B(\operatorname{Sym}^N H)$. For a unit vector $\psi$, an effect $0\le a\le I$ and an output site $k$, write $a_{(k)}$ for $a$ on that site. Define
--   $$
--   \Delta_{\mathrm{one}}(T)=\sup_{\|\psi\|=1,\,0\le a\le I,\,1\le k\le M}\left|\langle\psi^{\otimes N},T(a_{(k)})\psi^{\otimes N}\rangle-\langle\psi,a\psi\rangle\right|.
--   $$
--   Let $P_r$ project onto the actual permutation-fixed subspace $\operatorname{Sym}^r H$, and put $D_r=\binom{d+r-1}{r}$. The map whose Schrödinger dual is $\widehat T_*(\rho)=(D_N/D_M)P_M(\rho\otimes I_{M-N})P_M$ is a cloning map, and
--   $$
--   \Delta_{\mathrm{one}}(T)\ge\Delta_{\mathrm{one}}(\widehat T)=\frac{d-1}{d}\left|1-\frac{N}{N+d}\frac{M+d}{M}\right|
--   $$
--   for every cloning map $T$. This is the sharp single-clone bound and its explicit attainment; no covariance or permutation invariance is imposed on $T$.
--
--   **Formalization Note** Bose operators are zero-extended corner matrices with identity $P_N$.
-- source:
--   Optimal Cloning of Pure States, Judging Single Clones, arXiv:quant-ph/9807010v1, PDF p. 3, Theorem 1, inequality and Eq.(3)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P45

noncomputable section

open scoped Matrix ComplexOrder

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Renew46.P45

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P26 (Mat)

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P45.unitaryMeasurable

/-- PDF pp.2–3, Theorem 1 inequality AND attainment by Eq.(3).
The false unrestricted iff is deferred separately. -/
theorem sharp_single_clone_bound (d N M : ℕ) (hd : 0 < d)
    (hN : 1 ≤ N) (hNM : N < M) :
    IsCloning (optimalCloner (d := d) (Nat.le_of_lt hNM)) ∧
    cloningError (optimalCloner (d := d) (Nat.le_of_lt hNM)) = sharpError d N M ∧
    ∀ T : CloneFunction d N M, IsCloning T → sharpError d N M ≤ cloningError T := by sorry

end QAlgorithms.Papers.Independent.Renew46.P45

end
