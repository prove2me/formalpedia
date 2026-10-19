-- Prove2me | Theorems.Thm_QSVT19_Main_lemma_6
-- name    : QSVT19.Main.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:28:23.564392+00:00
-- url     : https://prove2.me/theorems/ba8e7bdf-d8ae-4443-975d-f82693d91bd2
-- title:
--   Lemma 6: a nonnegative even polynomial on $[-1,1]$ is $B^2+(1-x^2)C^2$ with degree and parity control
-- statement:
--   Let $k\in\mathbb N$ and let $A\in\mathbb R[x]$ be an even polynomial with $\deg A\le 2k$ and $A(x)\ge0$ for all $x\in[-1,1]$. Then there are $B,C\in\mathbb R[x]$ with
--   $$A(x)=B(x)^2+(1-x^2)\,C(x)^2,$$
--   where $\deg B\le k$, $\deg C\le k-1$, $B$ has parity $k\bmod 2$ and $C$ has parity $k-1\bmod 2$.
--
--   This sum-of-squares factorization is the polynomial core of the characterizations of quantum signal processing (Theorems 4 and 5).
--
--   **Formalization Note** The identity is between polynomials. $\deg C\le k-1$ is written $\deg C<k$, so $C=0$ when $k=0$; parities of real polynomials are stated for their complexifications.
-- source:
--   Gilyén, Su, Low, Wiebe, arXiv:1806.01838v1, p. 11, Lemma 6

import Definitions.Def_QSVT19_Main_Setting

set_option autoImplicit false

open scoped ComplexOrder
open Polynomial Matrix

namespace QSVT19.Main

/-- Gilyén, Su, Low, Wiebe, arXiv:1806.01838v1, Lemma 6, p. 11: "Suppose that A ∈ R[x] is an even polynomial such that deg(A) ≤ 2k and
for all x ∈ [−1, 1] we have A(x) ≥ 0. Then there exist polynomials B, C ∈ R[x] such that
A(x) = B^2(x) + (1 − x^2)C^2(x), moreover deg(B) ≤ k, deg(C) ≤ k − 1, B has parity-(k mod 2) and
C has parity-(k − 1 mod 2)."

**Formalization Note.** "A is even" is `A.comp (−X) = A`. The identity `A = B² + (1 − X²)C²` is
an identity of polynomials (equivalently, for all real `x`). "deg(C) ≤ k − 1" is `C.degree < k`
(so `k = 0` forces `C = 0`), and "parity-(k − 1 mod 2)" is `HasParity _ (k + 1)`; parities of
real polynomials are stated for their images in `ℂ[X]`. -/
theorem lemma_6 (k : ℕ) (A : ℝ[X]) (hA_even : A.comp (-X) = A) (hA_deg : A.degree ≤ (2 * k : ℕ))
    (hA_nonneg : ∀ x ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ A.eval x) :
    ∃ B C : ℝ[X], A = B ^ 2 + (1 - X ^ 2) * C ^ 2 ∧ B.degree ≤ k ∧ C.degree < k ∧ QAlgorithms.HasParity (B.map Complex.ofRealHom) k ∧ QAlgorithms.HasParity (C.map Complex.ofRealHom) (k + 1) := by sorry

end QSVT19.Main
