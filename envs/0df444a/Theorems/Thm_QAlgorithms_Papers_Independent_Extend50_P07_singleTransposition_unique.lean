-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P07_singleTransposition_unique
-- name    : QAlgorithms.Papers.Independent.Extend50.P07.singleTransposition_unique
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:46:29.292129+00:00
-- url     : https://prove2.me/theorems/e424f4f9-b83e-4146-bdc9-98484518bde4
-- title:
--   Lemma 10: unique successful transpose supermap and extension
-- statement:
--   Let $1\le d\le D$ be positive integer dimensions with fixed computational bases. Write $\mathcal E_V(X)=VXV^\dagger$ for an unknown isometry $V:\mathbb C^d\to\mathbb C^D$, where $V^\dagger V=I_d$. A protocol, including its finite memory and all its operations, is fixed before $V$. Its $k$ oracle slots receive the same channel $\mathcal E_V$, and every map identity below holds on every input operator. The uniform coefficient $p\in[0,1]$ is the scale in Eq. (5); the physical outcome probability on a density matrix $\rho$ is $p\operatorname{Tr}(f(V)(\rho))$.
--
--   Let $A$ be a physical one-slot general superinstrument whose successful branch exactly transposes every isometry with the same coefficient $p\in[0,1]$. Write $S$ for its unnormalized Choi operator, with oracle registers $I_1\simeq\mathbb C^d$, $O_1\simeq\mathbb C^D$, past $P\simeq\mathbb C^D$, and future $F\simeq\mathbb C^d$. Then
--
--   $$S=pDd\,|\Phi_D^+\rangle\langle\Phi_D^+|_{PO_1}\otimes|\Phi_d^+\rangle\langle\Phi_d^+|_{I_1F},$$
--
--   where $|\Phi_n^+\rangle=n^{-1/2}\sum_{i=0}^{n-1}|i,i\rangle$. Furthermore, for every linear input map $\Lambda$,
--
--   $$A_{\rm succ}(\Lambda)=p\Lambda^T.$$
--
--   The extension is a conclusion, not an assumption. In Choi coordinates, $\Lambda^T$ swaps the input and output legs without conjugating their coefficients. This characterizes the entire successful supermap beyond the isometry test family.
-- source:
--   Universal construction of decoders from encoding black boxes, arXiv:2110.00258v5, PDF p. 38, Appendix E.2 Lemma 10: uniqueness of the successful transpose supermap

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

/-- arXiv:2110.00258v5 PDF pp.38--40, Lemma 10: the Choi operator is
uniquely determined, and the branch transposes every linear map, not only isometries.
The delta formula is Eq. (155) after expanding its normalized Bell projectors. -/
theorem singleTransposition_unique (d D : ℕ) (hd : 0 < d) (hD : d ≤ D)
    (A : General d D D d 1) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hA : ∀ V : Isometry d D, ∀ X,
      A.run V X = (p : ℂ) • conjSuperop V.val.transpose X) :
    choi A.success = transposeSuperChoi d D p ∧
    ∀ J : Choi (Fin d) (Fin D),
      A.success (oneSlot J) = (p : ℂ) • transposeChoi J := by sorry

end QAlgorithms.Papers.Independent.Extend50.P07

end
