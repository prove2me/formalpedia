-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P12_lemma2_1
-- name    : QAlgorithms.Papers.Independent.Claimed50.P12.lemma2_1
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T18:30:23.121151+00:00
-- url     : https://prove2.me/theorems/15cbfa6d-1cc8-4299-8c0c-8bb964c0e6d4
-- title:
--   Relative entropy from dominated approximants
-- statement:
--   Let $\rho$ be a density operator and $\sigma\ge0$ on a nonzero finite-dimensional complex Hilbert space. Write $D$ for normalized relative entropy in bits, with $+\infty$ on support failure, and $\Delta(X,Y)=\tfrac12\|X-Y\|_1+\tfrac12|\operatorname{tr}(X-Y)|$. Let $s\in\mathbb R$ and let $\bar\rho_n\ge0$ satisfy $\bar\rho_n\le2^{sn}\sigma^{\otimes n}$ for every positive integer $n$. If the real limit $\lim_n\Delta(\bar\rho_n,\rho^{\otimes n})$ exists and is less than one, then
--
--   $$D(\rho\|\sigma)\le s.$$
--
--   No trace upper bound on the approximants is required. This criterion converts asymptotic operator domination into a relative entropy bound.
-- source:
--   Quantum conditional mutual information and approximate Markov chains, arXiv:1410.0664v3, PDF p. 5, Lemma 2.1

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P12

noncomputable section

open Filter MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P12

open QAlgorithms.Papers.Independent.Information100.P32 (Op)

open QAlgorithms.Papers.Independent.Information100.P69 (CP matrixPower permute)

open QAlgorithms.Papers.Independent.Information100.P80 (OperatorLE groupedPower)

open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

/-- Lemma 2.1 (PDF p.5). Positive copy counts n+1, actual limit, no trace cap on bar. -/
theorem lemma2_1 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (rho sigma : Op I) (hrho : IsDensityMatrix rho) (hsigma : sigma.PosSemidef)
    (s : ℝ) (bar : (n : ℕ) → Op (Fin (n+1) → I))
    (hbar : ∀ n, (bar n).PosSemidef)
    (hbound : ∀ n, OperatorLE (bar n) (((2 : ℝ) ^ (s * ((n+1 : ℕ) : ℝ)) : ℂ) • matrixPower sigma (n+1)))
    (hlimit : ∃ ell : ℝ, ell < 1 ∧
      Tendsto (fun n => generalizedTraceDistance (bar n) (matrixPower rho (n+1))) atTop (nhds ell)) :
    normalizedRelativeEntropyBits rho sigma ≤ (s : EReal) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P12

end
