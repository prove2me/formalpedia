-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_constantCompositionCoding
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.constantCompositionCoding
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:41:54.804986+00:00
-- url     : https://prove2.me/theorems/b56110a4-6162-4314-a87c-2edc52bb9f62
-- title:
--   Theorem II.18: For empirical P and R<I(P;W), codes have |M|≥(n+1)^(d−ad)2^(nR), e≤8(n+1)^(ad)2^(−nEg(R,P)), if n≥n0(a,d,P).
-- statement:
--   Fix a finite stationary channel $W$ with input alphabet size $a$ and output dimension $d$. Let $P$ be a realizable length-$n$ empirical law, $n>0$ and $R<I(P;W)$. Here $E_g(R,P)=\sup_{R\le L'-L}\min\{\mu_i(L,P),\tfrac12\mu_c(L',P)\}$, where $\mu_i=\inf_{H(V\mid P)>L}D(V\Vert W\mid P)$ and $\mu_c=\inf_{H(\nu)\le L'}D(\nu\Vert PW)$. For fixed $a,d,P$, one threshold $n_0(a,d,P)$ works for every channel $W$, every realizable positive length $n$, and every $R<I(P;W)$.
--
--   $$
--   |M|\ge(n+1)^{d-ad}2^{nR},\quad e\le8(n+1)^{ad}2^{-nE_g(R,P)}\quad(n\ge n_0(a,d,P),\ R<I(P;W)).
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 34, Theorem II.18

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P43

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P43

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

open QAlgorithms.Papers.Independent.Information100.P06 (Below)

open QAlgorithms.Papers.Independent.Information100.P60 (copies relativeBits)

open QAlgorithms.Papers.Independent.Dependency50.P19 (count both)

open QAlgorithms.Papers.Independent.Information100.P22 (coherentInformation)

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P40 (InBlocks)

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P43.matrixMeasurableSpace

/-- Theorem II.18, PDF pp.34-35: retain the negative polynomial prefactor and
factor 8. The printed n0(a,d,P) precedes the channel W, block length and rate R.
The proof's small-error transition caveat is recorded without weakening this
fully pinned theorem. -/
theorem constantCompositionCoding {a d : ℕ} (ha : 0 < a) (hd : 0 < d)
    (P : PMF (Fin a)) :
    ∃ n0 : ℕ, ∀ (W : FiniteChannel a (fullAlgebra d hd)) (n : ℕ), 0 < n → n0 ≤ n →
      (∃ w : Fin n → Fin a, ∀ x, empiricalWeight w x = (P x).toReal) →
      ∀ R : ℝ, R < W.information P →
      ∃ c : FiniteCode W n, c.Composition P ∧
        (c.messages : ℝ) ≥ (n+1 : ℝ)^((d : ℤ) - (a : ℤ)*d) * exp2 (n * R) ∧
        c.error ≤ 8 * (n+1 : ℝ)^(a*d) * divergenceTail n (greedyExponent W R P) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
