-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P36_coset_tensor_powers
-- name    : QAlgorithms.Papers.Independent.Gap48.P36.coset_tensor_powers
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:01:34.814731+00:00
-- url     : https://prove2.me/theorems/50067c81-5423-4925-806c-a7f66df29e3a
-- title:
--   Theorem 16, sufficient infinity-norm tensor-power clause
-- statement:
--   All Hilbert spaces have positive finite dimension. Channels are completely positive and trace preserving; conjugates use the same normalized pure-environment dilation. Use $X|k\rangle=|k+1\bmod d\rangle$, $Z|k\rangle=e^{2\pi ik/d}|k\rangle$, $W_{jk}=X^jZ^k$, and labels $(j,k)\in(\mathbb Z/d\mathbb Z)^2$. Write $\nu_p(\Phi)=\sup_\rho\|\Phi(\rho)\|_p$ and $S_{\min}(\Phi)=\inf_\rho S(\Phi(\rho))$, with density inputs, Schatten norm, and von Neumann entropy. For $d\ge2$, arrange the probability weights of a Pauli channel bijectively into a nonincreasing row-major array $b_{jk}$. Assume the rows are the cosets of a single $d$-element subgroup of the additive label group. For every integer $r\ge2$ with $b_{0,d-1}^r>b_{00}^{r-1}b_{10}$,
--
--   $$
--   \nu_\infty(\Phi^{\otimes r})=\nu_\infty(\Phi)^r.
--   $$
--
--   The identity row need not be the largest-weight row. The case $r=2$ gives (74), and attainment is not added as a hypothesis.
-- source:
--   Properties of Conjugate Channels with Applications to Additivity and Multiplicativity, arXiv:quant-ph/0509126v3, PDF p. 25, Theorem 16, sufficient infinity-norm tensor-power clause

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P36

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P36

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Claimed50.P48

open QAlgorithms.Papers.Independent.Information100.P67 (receiverChannel complementaryChannel)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy normalizedChoi)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P03 (convexRoof)

open QAlgorithms.Papers.Independent.Dependency50.P45 (holevoCapacity)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D E K L A2 B2 C2 : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype E] [DecidableEq E] [Fintype K] [DecidableEq K]

variable [Fintype L] [DecidableEq L] [Fintype A2] [DecidableEq A2]

variable [Fintype B2] [DecidableEq B2] [Fintype C2] [DecidableEq C2]

/-- Theorem 16 sufficient tensor-power clause, PDF pp.25–26.
The indexed coset premise precedes the extra strict inequality. No attainment
conclusion is assumed. The identity coset may be any row.
Correction to (73): equal weight values are replaced by indexed row images,
so tied weights retain the d-element partition specified by the rearrangement. -/
theorem coset_tensor_powers (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (a : WeylLabel d → ℝ) (ha : ProbabilityWeights a)
    (e : (Fin d × Fin d) ≃ WeylLabel d) (hs : SortedRows a e) (hc : CosetRows e)
    (r : ℕ) (hr : 2 ≤ r)
    (hstrict : a (e (0,Fin.rev (0 : Fin d))) ^ r >
      a (e (0,0)) ^ (r-1) * a (e (1,0))) :
    nu ⊤ (piSuperop (fun _ : Fin r => randomUnitary (finWeyl d) a)) =
      nu ⊤ (randomUnitary (finWeyl d) a) ^ r := by sorry

end QAlgorithms.Papers.Independent.Gap48.P36

end
