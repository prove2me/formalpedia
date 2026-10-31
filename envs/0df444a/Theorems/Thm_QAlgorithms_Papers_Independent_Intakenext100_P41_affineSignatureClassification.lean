-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P41_affineSignatureClassification
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P41.affineSignatureClassification
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:34:47.587739+00:00
-- url     : https://prove2.me/theorems/e66ba4bf-6ddb-4deb-96c6-f306b6f76e72
-- title:
--   Regular and singular affine signature orbits
-- statement:
--   Let $N\ge2$, $\ell\ge1$, $\Lambda_0=(N+\ell)\{a\in\mathbb Z^N:\sum_i a_i=0\}$, $W=\Lambda_0\rtimes S_N$, and $\delta=(N-1,N-2,\ldots,0)$. For every $m\in\mathbb Z^N$,
--
--   $$\operatorname{Stab}_W(m)=\{1\}\ \Longleftrightarrow\ m=w(f+\delta)\text{ for a unique pair }(w,f),$$
--
--   where $w\in W$ and $f_1\ge\cdots\ge f_N$ is an integral signature with $f_1-f_N\le\ell$. Also,
--
--   $$\operatorname{Stab}_W(m)\ne\{1\}\ \Longleftrightarrow\ \exists\text{ transposition }\sigma\in S_N:\ \sigma(m)-m\in\Lambda_0.$$
--
--   The representative $f$ is unnormalized; imposing $f_N=0$ would destroy the statement since affine translations preserve coordinate sum.
-- source:
--   Operator Algebras and Conformal Field Theory III. Fusion of positive energy representations of LSU(N) using bounded operators, arXiv:math/9806031v1, PDF p. 43, §34: Corollary

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P41

noncomputable section

open scoped BigOperators

open MeasureTheory Set

namespace QAlgorithms.Papers.Independent.Intakenext100.P41

/-- §34 corollary, PDF p.43: uniqueness is for the affine element AND the
unnormalized permissible signature. Enforcing f_N=0 here would be false because
the affine group preserves coordinate sum. Singular points have a transposition
congruence; the transposition need not fix the point in Z^N. -/
theorem affineSignatureClassification (N ell : ℕ) (hN : 2 ≤ N) (hell : 1 ≤ ell)
    (m : Fin N → ℤ) :
    (HasTrivialStabilizer ell m ↔
      ∃! p : AffineWeylElement N × {f : IntegerSignature N // IsPermissible ell f},
        affineAction ell p.1 (p.2.val + weylShift N) = m) ∧
    (¬HasTrivialStabilizer ell m ↔
      ∃ i j : Fin N, i ≠ j ∧ InAffineRootLattice ell
        (fun a => m ((Equiv.swap i j).symm a) - m a)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P41

end
