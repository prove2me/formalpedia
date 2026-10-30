-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P07_antisymmetricDecoder_fullAction
-- name    : QAlgorithms.Papers.Independent.Extend50.P07.antisymmetricDecoder_fullAction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:39:39.305857+00:00
-- url     : https://prove2.me/theorems/f28aaa9f-426d-491c-87e3-f1e4a39fcb10
-- title:
--   Theorem 2: antisymmetric decoder and its off-code action
-- statement:
--   Let $1\le d\le D$ be positive integer dimensions with fixed computational bases. Write $\mathcal E_V(X)=VXV^\dagger$ for an unknown isometry $V:\mathbb C^d\to\mathbb C^D$, where $V^\dagger V=I_d$. A protocol, including its finite memory and all its operations, is fixed before $V$. Its $k$ oracle slots receive the same channel $\mathcal E_V$, and every map identity below holds on every input operator. The uniform coefficient $p\in[0,1]$ is the scale in Eq. (5); the physical outcome probability on a density matrix $\rho$ is $p\operatorname{Tr}(f(V)(\rho))$.
--
--   There is a physical parallel protocol with $d-1$ oracle slots whose successful branch is $d^{-2}R_V$ for every isometry, where
--
--   $$R_V(Y)=V^\dagger YV+I_d\operatorname{Tr}((I_D-VV^\dagger)Y).$$
--
--   The map $R_V$ is CP and $R_V(\mathcal E_V(X))=X$ for every $X$. Thus the coefficient on encoded density matrices is $1/d^2$. The formula also specifies the full action away from the code; the second term contains $I_d$ without a factor $1/d$. It reduces to the trace decoder when $d=1$. This stronger map identity distinguishes the decoder from a trace-preserving completion.
-- source:
--   Universal construction of decoders from encoding black boxes, arXiv:2110.00258v5, PDF p. 7, §3.1 Theorem 2: antisymmetric decoder and full off-code action

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

/-- arXiv:2110.00258v5 PDF p.7, Theorem 2 and pp.43--45, Eq. (236):
Figure 2(b) has scale 1/d² and implements the full CP decoder of Eq. (7).
The description as CPTP in Appendix G is a typo: the off-code trace can exceed one. -/
theorem antisymmetricDecoder_fullAction (d D : ℕ) (hd : 0 < d) (hD : d ≤ D) :
    ∃ A : Parallel d D D d (d - 1), ∀ V : Isometry d D,
      FiniteKrausCP (decoder V) ∧ (∀ X, decoder V (conjSuperop V.val X) = X) ∧
      (∀ Y, A.run (oracleCopies (d - 1) V) Y =
        ((1 / (d : ℝ)^2 : ℝ) : ℂ) • decoder V Y) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P07

end
