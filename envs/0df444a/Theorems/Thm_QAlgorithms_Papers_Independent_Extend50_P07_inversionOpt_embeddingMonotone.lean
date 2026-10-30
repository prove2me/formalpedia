-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P07_inversionOpt_embeddingMonotone
-- name    : QAlgorithms.Papers.Independent.Extend50.P07.inversionOpt_embeddingMonotone
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:47:25.469029+00:00
-- url     : https://prove2.me/theorems/fbca1d41-3016-4ae2-a045-ea33b1365575
-- title:
--   Eq. (8): embedding monotonicity of the inversion optimum
-- statement:
--   Let $1\le d\le D$ be positive integer dimensions with fixed computational bases. Write $\mathcal E_V(X)=VXV^\dagger$ for an unknown isometry $V:\mathbb C^d\to\mathbb C^D$, where $V^\dagger V=I_d$. A protocol, including its finite memory and all its operations, is fixed before $V$. Its $k$ oracle slots receive the same channel $\mathcal E_V$, and every map identity below holds on every input operator. The uniform coefficient $p\in[0,1]$ is the scale in Eq. (5); the physical outcome probability on a density matrix $\rho$ is $p\operatorname{Tr}(f(V)(\rho))$.
--
--   Let $k\ge0$ and let $d\le D'\le D$. Write $p_{\rm opt}(d,D,k)$ for the optimal uniform coefficient of physical parallel inversion using $k$ oracle slots. Then
--
--   $$p_{\rm opt}(d,D,k)\le p_{\rm opt}(d,D',k).$$
--
--   The quantification includes every intermediate output dimension $D'$, not just $D'=d$. This is the source's embedding comparison, retained separately from the stronger dimension-independence theorem.
-- source:
--   Universal construction of decoders from encoding black boxes, arXiv:2110.00258v5, PDF p. 8, §3.1 Eq.(8): inversion optimum monotone in output dimension

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

/-- arXiv:2110.00258v5 PDF p.8, Eq. (8), and pp.14--15: monotonicity
under every intermediate output dimension, not just the square case. -/
theorem inversionOpt_embeddingMonotone (d Dsmall Dlarge k : ℕ)
    (hd : 0 < d) (hsmall : d ≤ Dsmall) (hlarge : Dsmall ≤ Dlarge) :
    inversionOpt d Dlarge k ≤ inversionOpt d Dsmall k := by sorry

end QAlgorithms.Papers.Independent.Extend50.P07

end
