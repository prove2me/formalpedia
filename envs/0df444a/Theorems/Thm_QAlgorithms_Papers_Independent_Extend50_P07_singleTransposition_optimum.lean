-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P07_singleTransposition_optimum
-- name    : QAlgorithms.Papers.Independent.Extend50.P07.singleTransposition_optimum
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:45:39.791285+00:00
-- url     : https://prove2.me/theorems/6494b06b-a8d8-4e9f-9ebd-df90702b4a4f
-- title:
--   Theorem 9: exact one-use transposition optimum
-- statement:
--   Let $1\le d\le D$ be positive integer dimensions with fixed computational bases. Write $\mathcal E_V(X)=VXV^\dagger$ for an unknown isometry $V:\mathbb C^d\to\mathbb C^D$, where $V^\dagger V=I_d$. A protocol, including its finite memory and all its operations, is fixed before $V$. Its $k$ oracle slots receive the same channel $\mathcal E_V$, and every map identity below holds on every input operator. The uniform coefficient $p\in[0,1]$ is the scale in Eq. (5); the physical outcome probability on a density matrix $\rho$ is $p\operatorname{Tr}(f(V)(\rho))$.
--
--   A fixed physical one-use parallel protocol attains the coefficient $1/(Dd)$ for isometry transposition. Conversely, if any physical one-slot general superinstrument implements the transpose with uniform coefficient $p\in[0,1]$, then
--
--   $$p\le\frac{1}{Dd}.$$
--
--   Consequently the attainable optimum is $p_{\rm opt}=1/(Dd)$. The upper bound covers the whole one-slot physical class, whose causal-order distinctions coincide. This optimizes the scale in Eq. (5), not a conditional probability normalized separately for each input.
-- source:
--   Universal construction of decoders from encoding black boxes, arXiv:2110.00258v5, PDF p. 38, Appendix E.2 Theorem 9: exact one-use transposition optimum

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

/-- arXiv:2110.00258v5 PDF pp.38--40, Theorem 9: attainable one-use
coefficient and its upper bound over the entire general physical class. -/
theorem singleTransposition_optimum (d D : ℕ) (hd : 0 < d) (hD : d ≤ D) :
    (∃ A : Parallel d D D d 1, ∀ V : Isometry d D, ∀ X,
      A.run (oracleCopies 1 V) X =
        ((1 / ((D : ℝ) * (d : ℝ)) : ℝ) : ℂ) • conjSuperop V.val.transpose X) ∧
    (∀ A : General d D D d 1, ∀ p : ℝ, 0 ≤ p → p ≤ 1 →
      (∀ V : Isometry d D, ∀ X,
        A.run V X = (p : ℂ) • conjSuperop V.val.transpose X) →
      p ≤ 1 / ((D : ℝ) * (d : ℝ))) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P07

end
