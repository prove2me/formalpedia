-- Prove2me | Theorems.Thm_PutermanMDP_Sensitive_rational_zeros
-- name    : PutermanMDP.Sensitive.rational_zeros
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:32:23.387472+00:00
-- url     : https://prove2.me/theorems/1ce7241f-9383-43db-81a3-d889c8c736a1
-- title:
--   Lemma 10.1.2 — zeros of a rational function
-- statement:
--   Let $I$ be a real interval and $f:I\to\mathbb R$ be rational, meaning $f(x)=p(x)/q(x)$ for real polynomials with $q(x)\ne0$ throughout $I$. If $f$ vanishes at some point of $I$, then
--   $$[\forall x\in I,\ f(x)=0]\quad\text{or}\quad\{x\in I:f(x)=0\}\text{ is finite}.$$
--   This is the chapter's rational-function dichotomy used in the existence argument.
--
--   **Formalization Note** The printed hypothesis of at least one zero is retained, although FINDINGS records that it is unnecessary.
-- source:
--   Puterman, Markov Decision Processes, Wiley, 1994, p. 496 (PDF 512), Lemma 10.1.2; https://doi.org/10.1002/9780470316887

import Mathlib

namespace PutermanMDP.Sensitive

theorem rational_zeros (I : Set ℝ) (hI : Set.OrdConnected I) (f : ℝ → ℝ)
    (hf : ∃ p q : Polynomial ℝ, (∀ x ∈ I, q.eval x ≠ 0) ∧
      ∀ x ∈ I, f x = p.eval x / q.eval x)
    (hzero : ∃ x ∈ I, f x = 0) :
    (∀ x ∈ I, f x = 0) ∨ {x : ℝ | x ∈ I ∧ f x = 0}.Finite := by sorry

end PutermanMDP.Sensitive
