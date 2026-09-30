-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_finite_jet_eliminant_iff
-- name    : WeierstrassEllipticZeta.finite_jet_eliminant_iff
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-12T23:35:08.811841+00:00
-- url     : https://prove2.me/theorems/135015a4-1936-4e61-98bd-3ca7b5627844
-- title:
--   Sharp degree criterion for finite jet vanishing
-- statement:
--   Let $X$ be a finite set of complex numbers, let $N$ be a natural number, and let $D$ be a real number. There exists a nonzero complex polynomial $P$ with degree at most $D$ such that
--   $$ P^{(k)}(x)=0\qquad(x\in X,\ 0\le k<N) $$
--   if and only if
--   $$ N|X|\le D. $$
--   Thus the minimum possible degree of a nonzero polynomial with these prescribed vanishing jets is exactly $N|X|$. The product
--   $$ \prod_{x\in X}(T-x)^N $$
--   attains this degree. The equivalence includes $N=0$, the empty set, and arbitrary real degree thresholds.
-- source:
--   Derived finite-jet degree criterion for the frontier https://prove2.me/theorems/80ebe548-4f16-47a2-b854-911464530876. The mission setting is Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2 and Theorem A.2, https://doi.org/10.1017/S001309152610145X. The polynomial criterion is proved here from Taylor coefficients and coprime root powers in Mathlib commit 0df444a360eaa60ab8c11dca51a86af692955474. It is a supporting reduction, not a claim to have proved the article's geometric multiplicity estimate.

import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.NormNum

theorem WeierstrassEllipticZeta.finite_jet_eliminant_iff
    (X : Finset ℂ) (N : ℕ) (D : ℝ) :
    (∃ P : Polynomial ℂ, P ≠ 0 ∧ (P.natDegree : ℝ) ≤ D ∧
      ∀ x ∈ X, ∀ k < N, (Polynomial.derivative^[k] P).eval x = 0) ↔
      (N : ℝ) * X.card ≤ D := by sorry
