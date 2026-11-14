-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_raw_eigenmatrix_gram
-- name    : QAlgorithms.Papers.Independent.Extend50.P31.raw_eigenmatrix_gram
-- status  : Open
-- author  : @Mrnaiq
-- created : 2026-11-14T05:56:10.63729+00:00
-- url     : https://prove2.me/theorems/9344f305-0a23-47ee-9bea-7867553af748
-- title:
--   Gram identity for all raw quantum-channel eigenmatrices
-- statement:
--   Under the finite-group irreducible and multiplicity-free decomposition assumptions, let $Q_r$ be a fine projector and let $V_r(p)=P_r(E_p)$ be its raw eigenmatrix at matrix-unit position $p$. For any fine sectors $r,s$ and positions $p,q$,
--
--   $$\langle V_r(p),V_s(q)\rangle_{\mathrm{HS}}=\begin{cases}(Q_r)_{pq}&r=s,\\0&r\ne s.\end{cases}$$
--
--   The inner product is conjugate-linear in its first argument and uses the unnormalized Hilbert–Schmidt convention. In particular, a raw eigenmatrix has squared norm equal to its diagonal pivot weight. The mixed Gram formula also records orthogonality across all distinct sectors.
-- source:
--   Mozrzymas, Studzinski and Datta, Structure of irreducibly covariant quantum channels for finite groups, https://arxiv.org/abs/1610.05657v2, PDF p.12 Proposition 17 Eq.(56), p.13 Proposition 20 Eqs.(62)–(63), and pp.31–32 Theorem 58 Eq.(157); mixed-position Gram extension of the displayed norm identity.

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P31
noncomputable section
open QAlgorithms.Papers.Independent.Extend50.P31
open QAlgorithms.Papers.Independent.Information100.P44 (Mat matrixUnit)
open QAlgorithms.Papers.Independent.Frontier18.P17 (hs res)
open scoped Matrix ComplexConjugate

theorem QAlgorithms.Papers.Independent.Extend50.P31.raw_eigenmatrix_gram {G A : Type*} [Group G] [Fintype G] [Fintype A] [DecidableEq A] {n : ℕ} (D : Data G A n) (r s : Row D) (p q : Fin n × Fin n) :
    hs (rawMatrix D.U D.F r.1.val r.2 p) (rawMatrix D.U D.F s.1.val s.2 q) =
      if r = s then fineMatrix D.U D.F r.1.val r.2 p q else 0 := by sorry
