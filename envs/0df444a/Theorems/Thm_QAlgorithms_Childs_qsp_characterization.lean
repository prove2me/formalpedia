-- Prove2me | Theorems.Thm_QAlgorithms_Childs_qsp_characterization
-- name    : QAlgorithms.Childs.qsp_characterization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:35:26.983925+00:00
-- url     : https://prove2.me/theorems/e3028154-2006-42ce-82a2-0882d03be1ce
-- title:
--   Quantum signal processing: which polynomial pairs a QSP sequence realizes
-- statement:
--   For $x\in[-1,1]$ let
--
--   $$W(x)=\begin{pmatrix} x & i\sqrt{1-x^2}\\ i\sqrt{1-x^2} & x\end{pmatrix}=e^{i\arccos(x)\sigma_x},$$
--
--   and for $\phi\in\mathbb R$ let $e^{i\phi\sigma_z}=\mathrm{diag}(e^{i\phi},e^{-i\phi})$. For $k\ge 0$ and a phase vector $\Phi=(\phi_0,\dots,\phi_k)\in\mathbb R^{k+1}$, the quantum signal processing sequence is
--
--   $$W_\Phi(x)=e^{i\phi_0\sigma_z}\,W(x)\,e^{i\phi_1\sigma_z}\,W(x)\cdots W(x)\,e^{i\phi_k\sigma_z},$$
--
--   with $k$ factors $W(x)$. For a polynomial $P\in\mathbb C[x]$ write $P^*$ for the polynomial with complex-conjugated coefficients (so $P^*(x)=\overline{P(x)}$ for real $x$).
--
--   **Lemma.** Let $k\ge0$ and $P,Q\in\mathbb C[x]$. There exists $\Phi\in\mathbb R^{k+1}$ such that for every $x\in[-1,1]$
--
--   $$W_\Phi(x)=\begin{pmatrix} P(x) & iQ(x)\sqrt{1-x^2}\\ iQ^*(x)\sqrt{1-x^2} & P^*(x)\end{pmatrix}$$
--
--   if and only if
--
--   1. $\deg P\le k$ and $\deg Q\le k-1$ (with $\deg 0=-\infty$; in particular $Q=0$ when $k=0$);
--   2. $P$ has parity $k \bmod 2$ and $Q$ has parity $k-1 \bmod 2$, where an even polynomial has parity $0$ and an odd one parity $1$, i.e. $P(-x)=(-1)^kP(x)$ and $Q(-x)=(-1)^{k-1}Q(x)$;
--   3. $|P(x)|^2+(1-x^2)|Q(x)|^2=1$ for all $x\in[-1,1]$.
--
--   This characterization is the core of quantum signal processing: it says exactly which polynomial transformations of a signal $x$ can be implemented by interleaving the signal rotation $W(x)$ with $z$-rotations, and it is later lifted, via qubitization, to polynomial transformations of block-encoded operators.
--
--   **Formalization Note** The matrix identity is required for all $x\in[-1,1]$, the domain on which $W(x)$ is defined in (29.6). The degree condition uses Mathlib's `degree` with values in $\mathbb N\cup\{-\infty\}$, so $\deg Q\le k-1$ is written $\deg Q<k$; the parity $k-1 \bmod 2$ of $Q$ is written as parity $k+1$, which is the same residue and avoids natural-number subtraction. Parity is the polynomial identity $P(-x)=(-1)^kP(x)$.
-- source:
--   Andrew Childs, Lecture Notes on Quantum Algorithms, 17 April 2025, PDF p. 152, Lemma 29.1. https://www.cs.umd.edu/~amchilds/qa/qa.pdf

import Definitions.Def_QAlgorithms_Defs_Hamiltonian
set_option autoImplicit false

namespace QAlgorithms.Childs

open Polynomial

/-- Childs, Lemma 29.1 (PDF p.152, citing [54, Theorem 3]): quantum signal processing.
For `k : ℕ` and `P, Q ∈ ℂ[x]`, there is `Φ ∈ ℝ^{k+1}` with
`W_Φ(x) = [[P(x), i Q(x) √(1−x²)], [i Q*(x) √(1−x²), P*(x)]]` for all `x ∈ [−1, 1]`
(the domain of `W(x)` in (29.6)) iff
(i) `deg P ≤ k` and `deg Q ≤ k − 1` (with `deg 0 = −∞`, so `Q = 0` when `k = 0`),
(ii) `P` has parity `k mod 2` and `Q` has parity `k − 1 ≡ k + 1 mod 2`, and
(iii) `|P(x)|² + (1 − x²)|Q(x)|² = 1` for all `x ∈ [−1, 1]`.
Here `P*` is `P` with conjugated coefficients. -/
theorem qsp_characterization (k : ℕ) (P Q : ℂ[X]) :
    (∃ Φ : Fin (k + 1) → ℝ, ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      qspSequence Φ x =
        !![P.eval (x : ℂ), Complex.I * Q.eval (x : ℂ) * (Real.sqrt (1 - x ^ 2) : ℂ);
          Complex.I * (Q.map (starRingEnd ℂ)).eval (x : ℂ) * (Real.sqrt (1 - x ^ 2) : ℂ),
          (P.map (starRingEnd ℂ)).eval (x : ℂ)]) ↔
    ((P.degree ≤ k ∧ Q.degree < k) ∧
      (HasParity P k ∧ HasParity Q (k + 1)) ∧
      ∀ x ∈ Set.Icc (-1 : ℝ) 1,
        ‖P.eval (x : ℂ)‖ ^ 2 + (1 - x ^ 2) * ‖Q.eval (x : ℂ)‖ ^ 2 = 1) := by
  sorry

end QAlgorithms.Childs
