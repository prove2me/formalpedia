-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P51_lemma_5_4
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P51.lemma_5_4
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:03:55.307815+00:00
-- url     : https://prove2.me/theorems/cd4ce36c-cbfd-42a9-9410-651eb8bb7532
-- title:
--   Lower contraction ideals enter the next layer
-- statement:
--   Let $r\ge1$ and let $R$ be a commutative unital ring. Fix units $q,\delta,\rho,u_1,\ldots,u_r$, with $\delta=q-q^{-1}$, and moments $\omega_a\in R$ for $a\in\mathbb Z$, with $\omega_0=1-\delta^{-1}(\rho-\rho^{-1})$. Write $B_{r,n}$ for the unital algebra with all relations of Definition 2.1; $T_i,E_i,X_j^{\pm1}$ denote its specified generators. Neither $\omega_0\ne0$ nor its invertibility is assumed. Assume $r=2p+1$ with $p\ge0$, and that $\Omega\cup\{\rho\}$ is $u$-admissible in Definition 3.15. A prime on $B_{r,m}'$ denotes its canonical image inside $B_{r,n}$, rather than an assumed embedding. Set $B_{r,0}'=R\cdot1$.
--
--   Let $n\ge1$ and $0\le2f\le n$. Put $E^f=E_{n-1}E_{n-3}\cdots E_{n-2f+1}$, $E^0=1$, and $B_{r,n}^g=B_{r,n}E^gB_{r,n}$, with the layer after $\lfloor n/2\rfloor$ set to zero. For $|\kappa_j|\le p$, write $X^\kappa=X_{n-1}^{\kappa_1}\cdots X_{n-2f+1}^{\kappa_f}$; these are precisely the active coordinates of $N_r^{f,n}$. If $\mathcal E_{n-2f}'$ is the image of the lower contraction ideal, then
--   $$ E^fX^\kappa z\in B_{r,n}^{f+1}\qquad\text{for every }z\in\mathcal E_{n-2f}'.$$
--   At lower levels $0$ and $1$ the contraction ideal is zero.
--
--   This is containment of a product submodule, not membership of an ideal in a single algebra element.
-- source:
--   The representations of cyclotomic BMW algebras, arXiv:0801.0465v2, PDF p. 35, Lemma 5.4

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P51

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Intakenext100.P51

section IdealFiltration

variable {R : Type*} [CommRing R] {r : ℕ} (P : Ground R r) (n : ℕ)

/-- Lemma 5.4, PDF p.35: containment for EVERY lower-ideal element, with
bounded exponents and the zero lower ideal at m=0,1. -/
theorem lemma_5_4 (p f : ℕ) (hr : r = 2*p+1) (hu : RuiXuUAdmissible P)
    (hf : 2*f ≤ n) (hn : 0 < n) (kappa : Fin f → ℤ)
    (hkappa : ∀ j, |kappa j| ≤ (p : ℤ)) :
    ∀ z ∈ lowerContraction P n (n-2*f),
      contractionChain P n f * exponentWord P n f kappa * z ∈ idealLayer P n (f+1) := by sorry

end IdealFiltration

end QAlgorithms.Papers.Independent.Intakenext100.P51

end
