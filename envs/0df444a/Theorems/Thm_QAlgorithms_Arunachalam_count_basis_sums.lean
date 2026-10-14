-- Prove2me | Theorems.Thm_QAlgorithms_Arunachalam_count_basis_sums
-- name    : QAlgorithms.Arunachalam.count_basis_sums
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:56:54.779749+00:00
-- url     : https://prove2.me/theorems/cf41a363-13b2-4140-9663-7e55360e14ae
-- title:
--   Counting index sequences whose basis vectors sum to S
-- statement:
--   Fix $S\in\{0,1\}^m$ with Hamming weight $|S|=q$, and let $e_1,\dots,e_m$ be the standard basis vectors of $\mathbb F_2^m$. For every integer $\ell$ with $q\le\ell\le T$, the number $N_\ell$ of sequences $(i_1,\dots,i_\ell)\in[m]^\ell$ with $e_{i_1}+\cdots+e_{i_\ell}=S$ (sum over $\mathbb F_2$) satisfies
--
--   $$
--   N_\ell\ \le\ \frac{\ell!\cdot m^{(\ell-q)/2}}{2^{(\ell-q)/2}\,((\ell-q)/2)!}\quad\text{if }\ell-q\text{ is even},\qquad N_\ell=0\quad\text{otherwise}.
--   $$
--
--   This combinatorial estimate controls the Fourier expansion of $(1-\beta|z|/m)^T$ in Lemma 7.5.4.
-- source:
--   Srinivasan Arunachalam, Quantum Algorithms and Learning Theory — Part II, 2018 thesis, ILLC DS-2018-08, PDF p. 173, Claim 7.5.5. https://ir.cwi.nl/pub/27536/Thesis_S_Arunachalam

import Definitions.Def_QAlgorithms_Defs_LearningHardInstances
set_option autoImplicit false

namespace QAlgorithms.Arunachalam

open QAlgorithms.Learning






/-- Arunachalam p.173, Claim 7.5.5: fix `S ∈ {0,1}^m` of Hamming weight `|S| = q`. For every
`ℓ ∈ {q, …, T}`, the number of index sequences `(i₁, …, i_ℓ) ∈ [m]^ℓ` with
`e_{i₁} + ⋯ + e_{i_ℓ} = S` (over `F₂`, `e_i` the `i`-th standard basis vector) is at most
`ℓ! · m^{(ℓ−q)/2} / (2^{(ℓ−q)/2} ((ℓ − q)/2)!)` if `ℓ − q` is even, and is `0` otherwise. -/
theorem count_basis_sums {m T ℓ : ℕ} (S : Fin m → ZMod 2) (hqℓ : hammingNorm S ≤ ℓ)
    (hℓT : ℓ ≤ T) :
    (Even (ℓ - hammingNorm S) →
        (((Finset.univ.filter fun i : Fin ℓ → Fin m =>
            ∑ j, Pi.single (i j) (1 : ZMod 2) = S).card : ℕ) : ℝ) ≤
          ((ℓ.factorial : ℕ) : ℝ) * (m : ℝ) ^ ((ℓ - hammingNorm S) / 2) /
            ((2 : ℝ) ^ ((ℓ - hammingNorm S) / 2) *
              (((ℓ - hammingNorm S) / 2).factorial : ℕ))) ∧
      (¬ Even (ℓ - hammingNorm S) →
        (Finset.univ.filter fun i : Fin ℓ → Fin m =>
            ∑ j, Pi.single (i j) (1 : ZMod 2) = S).card = 0) := by
  sorry

end QAlgorithms.Arunachalam
