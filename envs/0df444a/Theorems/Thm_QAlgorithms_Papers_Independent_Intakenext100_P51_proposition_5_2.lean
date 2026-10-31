-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P51_proposition_5_2
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P51.proposition_5_2
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:03:17.515843+00:00
-- url     : https://prove2.me/theorems/9d839b5b-d8fc-49a9-ac0f-88e595c84398
-- title:
--   The specified Hecke quotient isomorphism is unique
-- statement:
--   Let $r\ge1$ and let $R$ be a commutative unital ring. Fix units $q,\delta,\rho,u_1,\ldots,u_r$, with $\delta=q-q^{-1}$, and moments $\omega_a\in R$ for $a\in\mathbb Z$, with $\omega_0=1-\delta^{-1}(\rho-\rho^{-1})$. Write $B_{r,n}$ for the unital algebra with all relations of Definition 2.1; $T_i,E_i,X_j^{\pm1}$ denote its specified generators. Neither $\omega_0\ne0$ nor its invertibility is assumed. Assume $r=2p+1$ with $p\ge0$, and that $\Omega\cup\{\rho\}$ is $u$-admissible in Definition 3.15. A prime on $B_{r,m}'$ denotes its canonical image inside $B_{r,n}$, rather than an assumed embedding. Set $B_{r,0}'=R\cdot1$.
--
--   Let $n\ge2$, let $\mathcal E_n=B_{r,n}E_1B_{r,n}$ be the two-sided ideal spanned by all $aE_1b$, and let $H_{r,n}$ be the normalized Ariki–Koike algebra of p.3, with $(g_i-q)(g_i+q^{-1})=0$ and $y_{i+1}=g_iy_ig_i$. There is a unique $R$-algebra isomorphism satisfying
--   $$\varepsilon_n:H_{r,n}\overset\sim\longrightarrow B_{r,n}/\mathcal E_n,\qquad \varepsilon_n(g_i)=T_i+\mathcal E_n,\quad\varepsilon_n(y_j)=X_j+\mathcal E_n$$
--   for $1\le i<n$ and $1\le j\le n$.
--
--   This identifies the quotient by the actual contraction ideal, with the specified generator correspondence and bijectivity.
-- source:
--   The representations of cyclotomic BMW algebras, arXiv:0801.0465v2, PDF p. 34, Proposition 5.2

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P51

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Intakenext100.P51

section RuiXuHecke

variable {R : Type*} [CommRing R] {r : ℕ}

variable (P : Ground R r) (n : ℕ)

local notation "g" => ruiXuFreeG R n

local notation "y" => ruiXuFreeY R n

local notation "c" => algebraMap R (FreeAlgebra R (HeckeLetter n))

/-- Proposition 5.2, PDF p.34: unique generator-preserving algebra isomorphism.
All Assumption 5.1 hypotheses are retained, including odd positive r and n>=2. -/
theorem proposition_5_2 (hn : 2 ≤ n) (hr : Odd r) (hu : RuiXuUAdmissible P) :
    ∃! h : RuiXuHecke P n ≃ₐ[R] RuiXuHeckeQuotient P n,
      (∀ i, 1 ≤ i → i < n → h (HG P n i) = toHeckeQuotient P n (T P n i)) ∧
      (∀ j, 1 ≤ j → j ≤ n → h (HY P n j) = toHeckeQuotient P n (ruiXuX P n j false)) := by sorry

end RuiXuHecke

end QAlgorithms.Papers.Independent.Intakenext100.P51

end
