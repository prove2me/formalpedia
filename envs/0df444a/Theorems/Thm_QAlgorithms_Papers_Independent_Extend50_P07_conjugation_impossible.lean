-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P07_conjugation_impossible
-- name    : QAlgorithms.Papers.Independent.Extend50.P07.conjugation_impossible
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:41:46.768104+00:00
-- url     : https://prove2.me/theorems/ca560c03-001d-4d12-81ff-6cc41dbbcab1
-- title:
--   Theorem 5: universal conjugation is impossible for D at least 2d
-- statement:
--   Let $1\le d\le D$ be positive integer dimensions with fixed computational bases. Write $\mathcal E_V(X)=VXV^\dagger$ for an unknown isometry $V:\mathbb C^d\to\mathbb C^D$, where $V^\dagger V=I_d$. A protocol, including its finite memory and all its operations, is fixed before $V$. Its $k$ oracle slots receive the same channel $\mathcal E_V$, and every map identity below holds on every input operator. The uniform coefficient $p\in[0,1]$ is the scale in Eq. (5); the physical outcome probability on a density matrix $\rho$ is $p\operatorname{Tr}(f(V)(\rho))$.
--
--   Suppose $D\ge2d$. For every finite integer $k\ge0$, every general physical $k$-slot superinstrument $A$, and every $p\in(0,1]$, it is impossible that
--
--   $$A_{\rm succ}(\mathcal E_V^{\otimes k})(X)=p\overline V X\overline V^{\dagger}\quad\text{for every }V,X.$$
--
--   Here the bar is entrywise conjugation in the computational basis. The general class includes indefinite causal order and preserves instruments under arbitrary ancillary input and output extensions of each slot. This is a no-go result for the entire physical class, not just parallel circuits; it makes no assertion for $d<D<2d$.
-- source:
--   Universal construction of decoders from encoding black boxes, arXiv:2110.00258v5, PDF p. 18, §4.1 Theorem 5: universal conjugation impossible for D≥2d

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

/-- arXiv:2110.00258v5 PDF pp.17--20, Theorem 5: every finite k and every
completely instrument-preserving protocol, including indefinite causal order. -/
theorem conjugation_impossible (d D k : ℕ) (hd : 0 < d) (hD : 2 * d ≤ D)
    (A : General d D d D k) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ¬ (∀ V : Isometry d D, ∀ X,
      A.run V X = (p : ℂ) • conjSuperop (V.val.map conj) X) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P07

end
