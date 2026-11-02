-- Prove2me | Theorems.Thm_RankOneBimatrix_BinSearch_extreme_lambda_size
-- name    : RankOneBimatrix.BinSearch.extreme_lambda_size
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-02T01:07:06.257384+00:00
-- url     : https://prove2.me/theorems/48e60cf2-cca3-41e3-b00f-88fdceef175d
-- title:
--   Polynomial bit size of $\lambda^*$ at extreme solutions
-- statement:
--   There is a polynomial $p$ with the following property. Let $m,n\ge1$ and let $A\in\mathbb Q^{m\times n}$, $a\in\mathbb Q^m$, $b\in\mathbb Q^n$ have combined bit length $L$; let $M\subseteq[m]$, $N\subseteq[n]$ and $\lambda'\in\mathbb Q$. Then
--
--   1. the $\lambda$-coordinate of every extreme point of the face $P(M,N)$ in (28) is a rational number of bit size at most $p(L)$;
--   2. the $\lambda$-coordinate of every extreme point of the feasible set of $P_{\max}(M,N,a,\lambda')$ or of $P_{\min}(M,N,a,\lambda')$ in (39) is a rational number of bit size at most $p(L+\operatorname{size}(\lambda'))$.
--
--   Bit size is Schrijver's encoding length $1+\lceil\log_2(|\text{num}|+1)\rceil+\lceil\log_2(\text{den}+1)\rceil$ (`ratSize`). This is the claim in the proof of Theorem 19 that the output $\lambda^*$ of the LPs, an extreme solution obtained from linear equations derived from $A,a,b$ (and $\lambda'$), has polynomial bit size (Schrijver 1986, Corollary 10.2a(iii)).
-- source:
--   Adsul, Garg, Mehta, Sohoni, von Stengel, Fast Algorithms for Rank-1 Bimatrix Games, arXiv:1812.04611v4, p. 22, proof of Theorem 19 ('the output lambda* ... has polynomial bit size (Schrijver, 1986, Corollary 10.2a(iii))'); Schrijver, Theory of Linear and Integer Programming (1986), Section 10.2

import Definitions.Def_RankOneBimatrix_BinSearch_Algorithm

namespace RankOneBimatrix.BinSearch
open Matrix

/-- Bit size of the `λ`-coordinate of extreme points (Schrijver, Cor. 10.2a):
for rational data, the `λ`-coordinate of every extreme point of `P(M,N)` is a
rational of size polynomial in `L`, and that of every extreme point of the
feasible set of `Pmax(M,N,a,λ')` or `Pmin(M,N,a,λ')` (rational `λ'`) is a rational
of size polynomial in `L + size(λ')`. -/
theorem extreme_lambda_size :
    ∃ p : Polynomial ℕ,
      ∀ (m n : ℕ), 0 < m → 0 < n →
      ∀ (A : Matrix (Fin m) (Fin n) ℚ) (a : Fin m → ℚ) (b : Fin n → ℚ)
        (M : Finset (Fin m)) (N : Finset (Fin n)) (lam' : ℚ),
        (∀ z ∈ Set.extremePoints ℝ (PFace (A.map (fun r => (r : ℝ)))
            (fun j => (b j : ℝ)) M N),
          ∃ q : ℚ, (q : ℝ) = z.1 ∧ ratSize q ≤ p.eval (inputSize A a b)) ∧
        (∀ z ∈ Set.extremePoints ℝ (PmaxFeas (A.map (fun r => (r : ℝ)))
            (fun i => (a i : ℝ)) (fun j => (b j : ℝ)) M N (lam' : ℝ)),
          ∃ q : ℚ, (q : ℝ) = z.1 ∧
            ratSize q ≤ p.eval (inputSize A a b + ratSize lam')) ∧
        (∀ z ∈ Set.extremePoints ℝ (PminFeas (A.map (fun r => (r : ℝ)))
            (fun i => (a i : ℝ)) (fun j => (b j : ℝ)) M N (lam' : ℝ)),
          ∃ q : ℚ, (q : ℝ) = z.1 ∧
            ratSize q ≤ p.eval (inputSize A a b + ratSize lam')) := by sorry

end RankOneBimatrix.BinSearch
