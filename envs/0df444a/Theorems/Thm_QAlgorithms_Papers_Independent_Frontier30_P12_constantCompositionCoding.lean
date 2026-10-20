-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P12_constantCompositionCoding
-- name    : QAlgorithms.Papers.Independent.Frontier30.P12.constantCompositionCoding
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T17:07:44.048237+00:00
-- url     : https://prove2.me/theorems/e839a0a5-fb30-4d6a-bc15-a93b411fc6a4
-- title:
--   Proposition 5: constant-composition HSW coding
-- statement:
--   Let $W:\mathcal X\to\mathcal S(\mathcal H)$ be a finite cq channel with normalized outputs on a positive-dimensional complex register, and fix a probability law $P$ that is a type at some positive length. For every $\epsilon,\delta>0$, there is $n_0$ independent of the codebook size $N$ such that, for each compatible $n\ge n_0$ and $N\ge1$, independent uniform sampling with replacement from $T_P^n$ satisfies
--
--   $$\log_2N\le n\bigl(I(P;W)-\delta\bigr)\ \Longrightarrow\ \Pr[C\text{ is }\epsilon\text{-good}]\ge1-\epsilon.$$
--
--   Here $I(P;W)$ is the Holevo information in bits, $W_{x^n}^n=\bigotimes_i W_{x_i}$, and $C=(U(i))_{i=1}^N$ is $\epsilon$-good precisely when there is a decoding POVM $(D_i)_{i=1}^N$ on $\mathcal H^{\otimes n}$ with
--
--   $$\frac1N\sum_{i=1}^N\operatorname{Tr}(W_{U(i)}^nD_i)\ge1-\epsilon.$$
--
--   This is an average-success assertion; sampled codewords may coincide. It is the paper's fixed-composition variant of Holevo--Schumacher--Westmoreland coding, proved in Appendix C.
-- source:
--   Distillation of secret key and entanglement from quantum states, arXiv:quant-ph/0306078v1, PDF p. 4, Proposition 5

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P12

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter Topology

namespace QAlgorithms.Papers.Independent.Frontier30.P12

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op Vec)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon labelInformation)

open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

/-- arXiv:quant-ph/0306078v1, PDF pp.4--5, Proposition 5, proof pp.13--14.
This is the fixed-composition modification of HSW [30,46]; collisions are allowed
and the POVM gives uniform average success, not worst-codeword success. -/
theorem constantCompositionCoding {X H : Type} [Fintype X] [Fintype H]
    [Nonempty X] [Nonempty H] (p : X → ℝ) (W : X → Op H)
    (hp : IsLaw p) (hW : ∀ x, QAlgorithms.IsDensityMatrix (W x))
    (htype : ∃ n, IsTypeLength p n) (eps delta : ℝ) (heps : 0 < eps) (hdelta : 0 < delta) :
    ∃ n0 : ℕ, ∀ n ≥ n0, IsTypeLength p n → ∀ m : ℕ, 0 < m →
      Real.logb 2 (m : ℝ) ≤ n * (labelInformation p W - delta) →
      1 - eps ≤ typeSampleProb p n m (fun C => GoodCode W C eps) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P12

end
