-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P07_pseudoConjugation_deterministic
-- name    : QAlgorithms.Papers.Independent.Extend50.P07.pseudoConjugation_deterministic
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:43:40.057999+00:00
-- url     : https://prove2.me/theorems/ea6c9279-b023-43da-9ca8-fa8ec77f749d
-- title:
--   Theorem 7: deterministic scaled pseudo conjugation
-- statement:
--   Let $1\le d\le D$ be positive integer dimensions with fixed computational bases. Write $\mathcal E_V(X)=VXV^\dagger$ for an unknown isometry $V:\mathbb C^d\to\mathbb C^D$, where $V^\dagger V=I_d$. A protocol, including its finite memory and all its operations, is fixed before $V$. Its $k$ oracle slots receive the same channel $\mathcal E_V$, and every map identity below holds on every input operator. The uniform coefficient $p\in[0,1]$ is the scale in Eq. (5); the physical outcome probability on a density matrix $\rho$ is $p\operatorname{Tr}(f(V)(\rho))$.
--
--   Define the full CP map
--
--   $$Q_V(X)=\overline V X\overline V^{\dagger}+\overline{I_D-VV^\dagger}\operatorname{Tr}(X).$$
--
--   There is a physical parallel protocol with $d-1$ oracle slots, with identically zero failure branch, whose output map is
--
--   $$\frac{1}{D-d+1}Q_V.$$
--
--   Moreover, $Q_V^T\circ\mathcal E_V=\operatorname{id}_d$, where transposition of a map means transposing its Kraus operators in the fixed computational bases. The protocol is deterministic: for a density matrix, $\operatorname{Tr}Q_V(\rho)=D-d+1$. The stated coefficient is the Eq. (5) scale. For $D=d$ it is one; for $d=1$ the physical output is the constant maximally mixed state.
-- source:
--   Universal construction of decoders from encoding black boxes, arXiv:2110.00258v5, PDF p. 22, §4.2 Theorem 7: deterministic implementation of a scaled pseudo conjugate

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

/-- arXiv:2110.00258v5 PDF pp.21--22, Theorem 7, proof pp.45--47:
the physical protocol is deterministic, and its Eq. (5) coefficient is 1/(D-d+1). -/
theorem pseudoConjugation_deterministic (d D : ℕ) (hd : 0 < d) (hD : d ≤ D) :
    ∃ A : Parallel d D d D (d - 1),
      (∀ X, A.post.branch true X = 0) ∧
      ∀ V : Isometry d D, FiniteKrausCP (pseudoConjugate V) ∧
        (∀ X, fromChoi (transposeChoi (choi (pseudoConjugate V))) (conjSuperop V.val X) = X) ∧
        (∀ X, A.run (oracleCopies (d - 1) V) X =
          ((1 / ((D : ℝ) - (d : ℝ) + 1) : ℝ) : ℂ) • pseudoConjugate V X) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P07

end
