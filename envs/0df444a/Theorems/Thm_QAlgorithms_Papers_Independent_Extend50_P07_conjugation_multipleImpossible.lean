-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P07_conjugation_multipleImpossible
-- name    : QAlgorithms.Papers.Independent.Extend50.P07.conjugation_multipleImpossible
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:42:34.610997+00:00
-- url     : https://prove2.me/theorems/3ae07d91-c045-4619-9e43-96d3445fc3ff
-- title:
--   Lemma 6: conjugation obstruction for a nontrivial multiple
-- statement:
--   Let $1\le d\le D$ be positive integer dimensions with fixed computational bases. Write $\mathcal E_V(X)=VXV^\dagger$ for an unknown isometry $V:\mathbb C^d\to\mathbb C^D$, where $V^\dagger V=I_d$. A protocol, including its finite memory and all its operations, is fixed before $V$. Its $k$ oracle slots receive the same channel $\mathcal E_V$, and every map identity below holds on every input operator. The uniform coefficient $p\in[0,1]$ is the scale in Eq. (5); the physical outcome probability on a density matrix $\rho$ is $p\operatorname{Tr}(f(V)(\rho))$.
--
--   Let $d'>1$ be an integer and set $D=dd'$. For every finite $k\ge0$, every general physical superinstrument $A$, and every $p\in(0,1]$, it is impossible that
--
--   $$A_{\rm succ}(\mathcal E_V^{\otimes k})(X)=p\overline V X\overline V^{\dagger}\quad\text{for all }V\in V_{\rm iso}(d,dd')\text{ and all }X.$$
--
--   Physicality includes complete ancillary preservation, so this includes all indefinite-order protocols. The strict condition $d'>1$ is essential; at $d=1$ the assertion retains the finite-copy pure-state conjugation obstruction. This is the separately numbered multiple-dimension lemma used in the general no-go theorem.
-- source:
--   Universal construction of decoders from encoding black boxes, arXiv:2110.00258v5, PDF p. 18, §4.1 Lemma 6: conjugation impossible when D is a nontrivial multiple of d

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

/-- arXiv:2110.00258v5 PDF pp.18--20, Lemma 6: nontrivial-multiple case,
including the pure-state conjugation obstruction when d=1. -/
theorem conjugation_multipleImpossible (d dPrime k : ℕ) (hd : 0 < d)
    (hPrime : 1 < dPrime) (A : General d (d * dPrime) d (d * dPrime) k)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ¬ (∀ V : Isometry d (d * dPrime), ∀ X,
      A.run V X = (p : ℂ) • conjSuperop (V.val.map conj) X) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P07

end
