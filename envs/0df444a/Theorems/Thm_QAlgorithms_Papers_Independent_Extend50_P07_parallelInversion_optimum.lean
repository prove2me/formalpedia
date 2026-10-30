-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P07_parallelInversion_optimum
-- name    : QAlgorithms.Papers.Independent.Extend50.P07.parallelInversion_optimum
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:38:27.437458+00:00
-- url     : https://prove2.me/theorems/40c9a40d-b807-4fc4-a518-6b114a212971
-- title:
--   Theorem 1: parallel inversion optimum and achievable bound
-- statement:
--   Let $1\le d\le D$ be positive integer dimensions with fixed computational bases. Write $\mathcal E_V(X)=VXV^\dagger$ for an unknown isometry $V:\mathbb C^d\to\mathbb C^D$, where $V^\dagger V=I_d$. A protocol, including its finite memory and all its operations, is fixed before $V$. Its $k$ oracle slots receive the same channel $\mathcal E_V$, and every map identity below holds on every input operator. The uniform coefficient $p\in[0,1]$ is the scale in Eq. (5); the physical outcome probability on a density matrix $\rho$ is $p\operatorname{Tr}(f(V)(\rho))$.
--
--   Let $k\ge0$ be an integer and let $p_{\rm opt}(d,D,k)$ be the supremum of coefficients achievable by physical parallel inversion protocols. An inverse is a CP map $R_V$ satisfying $R_V\circ\mathcal E_V=\operatorname{id}_d$; it need not preserve trace away from the code. The optimum is attained, and
--
--   $$p_{\rm opt}(d,D,k)=p_{\rm opt}(d,d,k).$$
--
--   For $d\ge2$, put $m=\lfloor k/(d-1)\rfloor$. A parallel protocol achieves
--
--   $$b(d,k)=\begin{cases}0,&m=0,\\ m/(d^2+m-1),&m\ge1.\end{cases}$$
--
--   For $d=2$, this coefficient is the optimum. The dimension-independence and attainment assertions also include $d=1$. The zero-port case is the abort protocol. This separates the general achievable bound from the qubit optimality result.
-- source:
--   Universal construction of decoders from encoding black boxes, arXiv:2110.00258v5, PDF p. 7, §3.1 Theorem 1: parallel inversion optimum and achievable bound (abstract seed)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P07

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Extend50.P07

open QAlgorithms.Papers.Independent.Information100.P75 (Mat)

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

open QAlgorithms.Papers.Independent.Information100.P06 (Choi)

open QAlgorithms.Papers.Independent.Information100.P34 (choi fromChoi)

open QAlgorithms.Papers.Independent.Claimed50.P48 (FiniteKrausCP)

open QAlgorithms.Papers.Independent.Advance50.P05 (RectangularInstrument)

open QAlgorithms.Papers.Independent.Dependency50.P05 (ChannelChoi)

/-- arXiv:2110.00258v5 PDF pp.7--8,14--15, Theorem 1: equality with the
unitary optimum, attainment, the achievable family, and qubit optimality. -/
theorem parallelInversion_optimum (d D k : ℕ) (hd : 0 < d) (hD : d ≤ D) :
    inversionOpt d D k = inversionOpt d d k ∧
    IsGreatest (inversionProbabilities d D k) (inversionOpt d d k) ∧
    (2 ≤ d → inversionBound d k ∈ inversionProbabilities d D k) ∧
    (d = 2 → IsGreatest (inversionProbabilities d D k) (inversionBound d k)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P07

end
