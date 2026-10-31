-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P51_corollary_4_27
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P51.corollary_4_27
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:02:50.469266+00:00
-- url     : https://prove2.me/theorems/05acf42e-7865-4ab5-8c7e-eed8f3224f3e
-- title:
--   Bounded neighbor expansions for both generator signs
-- statement:
--   Let $r\ge1$ and let $R$ be a commutative unital ring. Fix units $q,\delta,\rho,u_1,\ldots,u_r$, with $\delta=q-q^{-1}$, and moments $\omega_a\in R$ for $a\in\mathbb Z$, with $\omega_0=1-\delta^{-1}(\rho-\rho^{-1})$. Let $B_{r,n}$ be the algebra of Definition 2.1 with all its specified relations. No nonzero or invertibility assumption on $\omega_0$ is made. Assume that the parameters are $\mathbf u$-admissible in the sense of Definition 3.15.
--
--   Let $a\in\mathbb Z$ and $1\le k<n$. For each $\varepsilon\in\{1,-1\}$ there are coefficients $f_i,g_i\in Z(B_{r,k-1})\cap R[X_1^{\pm1},\ldots,X_{k-1}^{\pm1}]$, evaluated canonically in the ambient algebra, such that
--   $$
--   \begin{aligned}
--   E_kX_k^aT_{k-1}^{\varepsilon}E_k&=\sum_{i=-|a|}^{|a|}f_iX_{k-1}^{i}E_k &&(2\le k<n),\\
--   E_kX_k^aT_{k+1}^{\varepsilon}E_k&=\sum_{i=-|a|}^{|a|}g_iX_{k+2}^{i}E_k &&(1\le k<n-1).
--   \end{aligned}
--   $$
--   The coefficients may depend on the neighbor and sign. Here $T_i^{-1}=T_i-\delta+\delta E_i$.
--
--   This controls the degree of the neighbor-variable expansion for every integer exponent. The printed bounds $-a$ and $a$ have been corrected to $-|a|$ and $|a|$, as required for negative exponents by the cited Lemma 2.3(4),(5). This source correction requires independent moderation.
-- source:
--   The representations of cyclotomic BMW algebras, arXiv:0801.0465v2, PDF p. 21, Corollary 4.27

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P51

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Intakenext100.P51

section CentralSeries

variable {R : Type*} [CommRing R] {r : ℕ} (P : Ground R r)

/-- Corollary 4.27, PDF p.21. SOURCE CORRECTION: the printed range -a..a
is empty for negative a; use -|a|..|a| as forced by Lemma 2.3(4),(5).
Both neighboring generators and both inverse choices are retained. Each
coefficient is a Laurent word central in the actual lower algebra, then
canonically evaluated in the ambient algebra. Independent moderation pending. -/
theorem corollary_4_27 (hu : RuiXuUAdmissible P) (n k : ℕ) (hk : 1 ≤ k ∧ k < n)
    (a : ℤ) :
    (2 ≤ k → ∀ inverse : Bool,
      ∃ f : ℤ → FreeAlgebra R (Fin (k-1) × Bool),
        (∀ i ∈ Finset.Icc (-|a|) |a|, CentralLaurentWord P (k-1) (f i)) ∧
        ruiXuE P n k * XPow P n k a * signedT P n (k-1) inverse * ruiXuE P n k =
          ∑ i ∈ Finset.Icc (-|a|) |a|,
            laurentEval P n (k-1) (f i) * XPow P n (k-1) i * ruiXuE P n k) ∧
    (k+1 < n → ∀ inverse : Bool,
      ∃ g : ℤ → FreeAlgebra R (Fin (k-1) × Bool),
        (∀ i ∈ Finset.Icc (-|a|) |a|, CentralLaurentWord P (k-1) (g i)) ∧
        ruiXuE P n k * XPow P n k a * signedT P n (k+1) inverse * ruiXuE P n k =
          ∑ i ∈ Finset.Icc (-|a|) |a|,
            laurentEval P n (k-1) (g i) * XPow P n (k+2) i * ruiXuE P n k) := by sorry

end CentralSeries

end QAlgorithms.Papers.Independent.Intakenext100.P51

end
