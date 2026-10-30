-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P23_systematic_toeplitz_condition1
-- name    : QAlgorithms.Papers.Independent.Advance50.P23.systematic_toeplitz_condition1
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T12:25:52.893289+00:00
-- url     : https://prove2.me/theorems/b12df19d-e716-4209-b223-05390bfc9b14
-- title:
--   Unnumbered p.9: systematic Toeplitz submodules satisfy Condition 1
-- statement:
--   All classical alphabets are finite and nonempty and all quantum systems are finite dimensional. A cq channel $W:x\mapsto W_x$ has positive semidefinite outputs of trace one; every input law is nonnegative and sums to one. Logarithms are natural. Write $I_s(W,P)$ for the paper's Petz information, $I_s^G(W,P)$ for its Gallager information, $H_{1+s}(P)$ for classical Rényi entropy, and $I_0=I_0^G=I$ for Holevo information. Matrix powers vanish on the kernel, including exponent zero. Write $\bar W_P=\sum_xP(x)W_x$, $A_s=\sum_xP(x)W_x^{1+s}$, $v$ for the number of distinct eigenvalues of $\bar W_P$, and $v_s$ for that of $A_s$. The supported spectral spread is $\lambda_s=\log\lambda_{\max}(A_s)-\log\lambda_{\min,+}(A_s)$ and $\mu_s=\min\{4+\sqrt{v_s},(4+\sqrt{\lceil\lambda_s\rceil})e^{s/2}\}$.
--
--   Over a finite field $K$ of size $q$, let $r,\ell\ge0$ and sample independent uniform Toeplitz diagonal seeds for an $r\times\ell$ matrix $T$. In $X=K^\ell\times K^r$, set $C_T=\{(a,Ta):a\in K^\ell\}$. Then
--   $$|C_T|=q^\ell,\qquad\Pr[x\in C_T]\le\frac{q^\ell}{q^{r+\ell}}\quad(x\ne0).$$
--   Thus this systematic ensemble satisfies Condition 1. Zero-height and zero-width matrices have their actual empty-entry law; no Condition 2 assertion is included.
--
--   This result supplies the corresponding finite-dimensional information or coding interface for the paper's security analysis.
-- source:
--   Quantum wiretap channel with non-uniform random number and its exponent and equivocation rate of leaked information, arXiv:1202.0325v3, PDF p. 9, Unnumbered p.9: systematic Toeplitz submodules satisfy Condition 1

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P23

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P23

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal

open Filter

open QAlgorithms.Papers.Independent.Information100.P56
  (IsLaw entropy average holevo uniform ProjectiveRep orbit productOutput)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Dependency50.P21 (IsSupported relativeEntropy)

open QAlgorithms.Papers.Independent.Dependency50.P28 (pinch logNonnegativeExtended)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {X A Z B E : Type} [Fintype X] [Fintype A] [Fintype Z]
  [Fintype B] [DecidableEq B] [Fintype E] [DecidableEq E]

/-- PDF p.9: the systematic Toeplitz image satisfies Condition 1. No assertion
about the printed invertible-top-block Condition 2 construction is made. -/
theorem systematic_toeplitz_condition1 {K : Type} [Field K] [Fintype K] (r l : ℕ) :
    Condition1 (uniform : (Fin (r + l - 1) → K) → ℝ)
      (systematicSubmodule (K := K) r l) ((Fintype.card K)^l) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P23

end
