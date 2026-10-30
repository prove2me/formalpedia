-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P05_principalEstimate
-- name    : QAlgorithms.Papers.Independent.Bridge50.P05.principalEstimate
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:59:02.662362+00:00
-- url     : https://prove2.me/theorems/0ee057f1-0b5d-4424-8e3a-8e94f7cb420b
-- title:
--   Theorem 1, principal estimate (2.3)
-- statement:
--   Let $d\ge1$, $H=\mathbb C^{\mathbb Z_d}$, and $Z=\mathbb Z_d\times\mathbb Z_d$. In the specified orthonormal basis let $W_{(x,y)}=U^xV^y$, where $Ue_k=e_{k+1}$ and $Ve_k=e^{2\pi i k/d}e_k$. Write $f_X(z)=\operatorname{Tr}(XW_z^*)/d$. All spaces are finite dimensional. The norm $\|X\|_2=\sqrt{\operatorname{Tr}(X^*X)}$ is the Hilbert–Schmidt norm, and $\nu_2(\Phi)=\sup_{\rho\ge0,\operatorname{Tr}\rho=1}\|\Phi(\rho)\|_2$ is the maximal output norm. A map in $W_1(H)$ is complex linear, Weyl covariant and satisfies $\Phi(I)=I$; it need not be positive or completely positive. Its computed symbol is $\phi(z)=f_{\Phi(W_z)}(z)$. Put $m(\phi)=\max_{z\ne0}|\phi(z)|^2$ and $E_{\max}(\phi)=\{z\ne0:|\phi(z)|^2=m(\phi)\}$. At $d=1$, explicitly set $m=0$ and $E_{\max}=\varnothing$. Write $S(\phi)=d^{-1/2}\sqrt{1+(d-1)m(\phi)}$.
--
--   For every $\Phi\in W_1(H)$, every finite ancillary space $K$, and every operator $X\in\mathcal M(H\otimes K)$,
--
--   $$\|(\Phi\otimes\operatorname{Id}_K)(X)\|_2^2\le\frac{1-m(\phi)}d\|\operatorname{Tr}_H X\|_2^2+m(\phi)\|X\|_2^2.$$
--
--   No positivity or normalization is required of $X$, and there is no contractivity or complete positivity hypothesis on $\Phi$. This is the principal operator estimate underlying the maximal-output bound.
-- source:
--   On Weyl-covariant channels, arXiv:quant-ph/0510148v3, PDF p. 4, Theorem 1, principal estimate (2.3)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P05

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P05

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Information100.P34 (cyclicPhase weyl dephasing)

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

open QAlgorithms.Papers.Independent.Gap48.P36 (WeylLabel)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Claimed50.P48
  (nu superopTensor UniversalMultiplicative rowKraus indexedKrausDilation)

open QAlgorithms.Papers.Independent.Information100.P67 (complementaryChannel)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {d : ℕ} [NeZero d]

/-- Theorem 1, PDF pp.4--5, (2.3): arbitrary joint operators, with no positivity,
trace-one, CP, or contractive-symbol hypothesis. -/
theorem principalEstimate (Phi : Op (ZMod d) →ₗ[ℂ] Op (ZMod d)) (hPhi : NormalizedWeylMap Phi)
    {K : Type*} [Fintype K] [DecidableEq K]
    (X : Matrix (ZMod d × K) (ZMod d × K) ℂ) :
    schattenNorm 2 (superopTensor Phi (fun Y : Matrix K K ℂ => Y) X) ^ 2 ≤
      (1 - maxSq (symbol Phi)) / (d : ℝ) * schattenNorm 2 (traceLeft X) ^ 2 +
      maxSq (symbol Phi) * schattenNorm 2 X ^ 2 := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P05

end
