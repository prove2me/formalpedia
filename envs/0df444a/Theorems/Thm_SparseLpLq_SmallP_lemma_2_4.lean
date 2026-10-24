-- Prove2me | Theorems.Thm_SparseLpLq_SmallP_lemma_2_4
-- name    : SparseLpLq.SmallP.lemma_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:45:57.233664+00:00
-- url     : https://prove2.me/theorems/73698b0f-543b-49b8-a9ec-9cd8e61ddbbb
-- title:
--   Lemma 2.4, p. 8 — log-moments Δ_k decide the order of ‖a‖_p^p and ‖b‖_p^p for all small p > 0
-- statement:
--   Let $a,b\in\mathbb R^n$ have the same number of nonzero entries, $\|a\|_0=\|b\|_0=s$. For $k=1,\dots,s$ let
--
--   $$\Delta_k(a,b):=\sum_{i:\,a_i\ne 0}(\ln|a_i|)^k-\sum_{i:\,b_i\ne 0}(\ln|b_i|)^k, \tag{2.5}$$
--
--   and write $\|x\|_p^p=\sum_i|x_i|^p$. Then:
--
--   1. if $\Delta_k(a,b)=0$ for all $k=1,\dots,s$, then $\|a\|_p^p=\|b\|_p^p$ for every $p>0$;
--   2. otherwise there is $p'>0$ such that either $\|a\|_p^p<\|b\|_p^p$ for every $p\in(0,p']$, or $\|a\|_p^p>\|b\|_p^p$ for every $p\in(0,p']$.
--
--   In words: two vectors of equal sparsity either have the same $\ell_p$ objective for all $p>0$, or one of them is strictly better than the other uniformly for all sufficiently small $p$. Theorem 2.2's stabilization clause rests on this dichotomy.
--
--   **Formalization Note** The paper lists the nonzero entries of $a$ and $b$ in order of increasing modulus before summing in (2.5); the sum does not depend on that order, so $\Delta_k$ is defined directly over the supports.
--
--   Differences from the source:
--   - reading: "there exists a sufficiently small p′ such that either ‖a‖_p^p < ‖b‖_p^p or ‖a‖_p^p > ‖b‖_p^p holds for any p ∈ (0, p′]" → ∃ p′ > 0, (∀ p ∈ (0, p′], ‖a‖_p^p < ‖b‖_p^p) ∨ (∀ p ∈ (0, p′], ‖b‖_p^p < ‖a‖_p^p); reason: the scope of "either … or … for any p" is ambiguous; this is the stronger, uniform reading, which is what Appendix B proves via (B.2)–(B.3) and what the proof of Theorem 2.2 (p. 8) uses
--   - encoding: Δ_k as a sum over the sorted nonzero entries a_{i_1}, …, a_{i_s} → the same sum over the unsorted support {i : aᵢ ≠ 0}; reason: a finite sum does not depend on the order of its terms
-- source:
--   Yang, Chen & Xiang, Sparse solutions of a class of constrained optimization problems, arXiv:1907.00880v5, p. 8, Lemma 2.4 and Equation (2.5); proof Appendix B, pp. 23–24

import Mathlib
import Definitions.Def_SparseLpLq_SmallP_Setting

open scoped ENNReal Matrix

namespace SparseLpLq.SmallP
theorem lemma_2_4 {n : ℕ} (a b : Fin n → ℝ) (s : ℕ)
    (ha : (Finset.univ.filter (fun i => a i ≠ 0)).card = s)
    (hb : (Finset.univ.filter (fun i => b i ≠ 0)).card = s) :
    ((∀ k ∈ Finset.Icc 1 s, Delta k a b = 0) → ∀ p : ℝ, 0 < p → lpObj p a = lpObj p b) ∧
      ((¬ ∀ k ∈ Finset.Icc 1 s, Delta k a b = 0) → ∃ p' > (0 : ℝ),
        (∀ p ∈ Set.Ioc 0 p', lpObj p a < lpObj p b) ∨
          (∀ p ∈ Set.Ioc 0 p', lpObj p b < lpObj p a)) := by sorry
end SparseLpLq.SmallP
