-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P07_pseudoConjugation_teleportationBound
-- name    : QAlgorithms.Papers.Independent.Extend50.P07.pseudoConjugation_teleportationBound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:49:20.726901+00:00
-- url     : https://prove2.me/theorems/0703363d-3562-462a-b850-b60719bdb1cd
-- title:
--   Pseudo conjugation followed by gate teleportation
-- statement:
--   Let $1\le d\le D$ be positive integer dimensions with fixed computational bases. Write $\mathcal E_V(X)=VXV^\dagger$ for an unknown isometry $V:\mathbb C^d\to\mathbb C^D$, where $V^\dagger V=I_d$. A protocol, including its finite memory and all its operations, is fixed before $V$. Its $k$ oracle slots receive the same channel $\mathcal E_V$, and every map identity below holds on every input operator. The uniform coefficient $p\in[0,1]$ is the scale in Eq. (5); the physical outcome probability on a density matrix $\rho$ is $p\operatorname{Tr}(f(V)(\rho))$.
--
--   There is a physical parallel inversion protocol using $d-1$ oracle calls and implementing the full decoder $R_V$ of Eq. (7) with coefficient
--
--   $$p_{\rm concat}=\frac{1}{Dd(D-d+1)}.$$
--
--   More generally let $q\in[0,1]$ and let $Q_V$ be any CP pseudo conjugate, so $Q_V^T\circ\mathcal E_V=\operatorname{id}_d$. Gate teleportation applied to the successful map $qQ_V$ acts on code inputs as
--
--   $$\mathcal T_{qQ_V}(\mathcal E_V(X))=\frac{q}{Dd}X,\qquad \frac{q}{Dd}\le\frac{1}{Dd}.$$
--
--   When $D>d$, even this upper bound is strictly below $1/d^2$, the antisymmetric decoder's coefficient. The strict comparison is not asserted when $D=d$. This bound is restricted to the stated concatenation strategy.
-- source:
--   Universal construction of decoders from encoding black boxes, arXiv:2110.00258v5, PDF p. 22, §4.2: pseudo conjugation followed by gate teleportation

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

/-- arXiv:2110.00258v5 PDF p.22: concatenation attains the stated coefficient;
any pseudo-conjugation followed by this teleportation has coefficient at most 1/(Dd).
The strict comparison requires D>d; the source's Figure 2(c) means Figure 2(b). -/
theorem pseudoConjugation_teleportationBound (d D : ℕ) (hd : 0 < d) (hD : d ≤ D) :
    (∃ A : Parallel d D D d (d - 1), ∀ V : Isometry d D, ∀ X,
      A.run (oracleCopies (d - 1) V) X =
        ((1 / ((D : ℝ) * (d : ℝ) * ((D : ℝ) - (d : ℝ) + 1)) : ℝ) : ℂ) •
          decoder V X) ∧
    (∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      q / ((D : ℝ) * (d : ℝ)) ≤ 1 / ((D : ℝ) * (d : ℝ)) ∧
      (d < D → q / ((D : ℝ) * (d : ℝ)) < 1 / (d : ℝ)^2) ∧
      ∀ V : Isometry d D, ∀ Q : Superop (Fin d) (Fin D), FiniteKrausCP Q →
        (∀ X, fromChoi (transposeChoi (choi Q)) (conjSuperop V.val X) = X) →
        ∀ X, gateTeleport (fun Y => (q : ℂ) • Q Y) (conjSuperop V.val X) =
          (((q / ((D : ℝ) * (d : ℝ)) : ℝ) : ℂ)) • X) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P07

end
