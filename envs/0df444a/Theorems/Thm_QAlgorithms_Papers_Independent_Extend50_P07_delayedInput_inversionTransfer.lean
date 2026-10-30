-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P07_delayedInput_inversionTransfer
-- name    : QAlgorithms.Papers.Independent.Extend50.P07.delayedInput_inversionTransfer
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:40:33.573914+00:00
-- url     : https://prove2.me/theorems/cc437118-40a6-4005-8564-2d217a115263
-- title:
--   Lemma 3: delayed-input inversion transfer
-- statement:
--   Let $1\le d\le D$ be positive integer dimensions with fixed computational bases. Write $\mathcal E_V(X)=VXV^\dagger$ for an unknown isometry $V:\mathbb C^d\to\mathbb C^D$, where $V^\dagger V=I_d$. A protocol, including its finite memory and all its operations, is fixed before $V$. Its $k$ oracle slots receive the same channel $\mathcal E_V$, and every map identity below holds on every input operator. The uniform coefficient $p\in[0,1]$ is the scale in Eq. (5); the physical outcome probability on a density matrix $\rho$ is $p\operatorname{Tr}(f(V)(\rho))$.
--
--   Let $k\ge0$, let $p\in[0,1]$, and supply an entire physical parallel delayed-input protocol $A$ for square $d$-dimensional unitary inversion. Thus the fixed resource is queried before the eventual input arrives, and for every unitary $U$ and every operator $X$,
--
--   $$A(\mathcal E_U^{\otimes k})(X)=pU^\dagger XU.$$
--
--   There exists a parallel delayed-input protocol $B$ using the same $k$ oracle slots and satisfying, for every $V$,
--
--   $$B(\mathcal E_V^{\otimes k})=pR_V,\qquad R_V\text{ CP},\qquad R_V\circ\mathcal E_V=\operatorname{id}_d.$$
--
--   The encoded input to $B$ is $D$-dimensional. The conclusion requires only a CP left inverse, not an adjoint channel on arbitrary off-code inputs. This transfers a supplied delayed-input resource rather than an arbitrary parallel realization.
-- source:
--   Universal construction of decoders from encoding black boxes, arXiv:2110.00258v5, PDF p. 9, §3.2 Lemma 3: delayed-input unitary-to-isometry inversion transfer

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

/-- arXiv:2110.00258v5 PDF p.9, Lemma 3, proof pp.10--14: transfer of
an entire supplied delayed-input protocol. Its unknown unitary is quantified last.
The encoded input register is D-dimensional as in Eqs. (17)--(20). -/
theorem delayedInput_inversionTransfer (d D k : ℕ) (hd : 0 < d) (hD : d ≤ D)
    (A : Delayed d d d d k) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hA : ∀ U : Isometry d d, ∀ X,
      A.run (oracleCopies k U) X = (p : ℂ) • conjSuperop U.valᴴ X) :
    ∃ B : Delayed d D D d k, ∀ V : Isometry d D,
      ExactInverse (B.run (oracleCopies k V)) p V := by sorry

end QAlgorithms.Papers.Independent.Extend50.P07

end
