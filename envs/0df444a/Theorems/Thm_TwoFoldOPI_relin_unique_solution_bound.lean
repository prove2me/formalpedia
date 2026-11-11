-- Prove2me | Theorems.Thm_TwoFoldOPI_relin_unique_solution_bound
-- name    : TwoFoldOPI.relin_unique_solution_bound
-- status  : Proved
-- author  : @sragavan
-- created : 2026-11-10T20:01:31.773413+00:00
-- url     : https://prove2.me/theorems/57de7180-a4b4-4ff1-aea9-87738e628d8a
-- title:
--   Lemma 7.3, core — the Schur-square relinearization has the unique solution $v=c$ except with probability $\le E$
-- statement:
--   Let $\mathbb F_q$ be a finite field, let $D\subseteq\mathbb F_q^m$ be a linear code (in the mission $D=C^\perp$), and let $c\in D$ be fixed. For $c'\in\mathbb F_q^m$ with $c'_i\neq c_i$ for every $i$, the unordered pairs $\{c_i,c'_i\}$ determine $a+a'=c+c'$ and $a\odot a'=c\odot c'$ for any ordering $(a_i,a'_i)$ of the pairs. Consider the linear relaxation of the constraints $(c-a)\odot(c-a')=0$:
--   $$w-(c+c')\odot v+c\odot c'=0,\qquad v\in D,\quad w\in D^{*2},$$
--   where $D^{*2}$ is the Schur square and $\odot$ the coordinate-wise product. The pair $(v,w)=(c,c\odot c)$ always solves it, and it is the only solution exactly when no solution has $v\neq c$.
--
--   If $c'$ is uniform on $\prod_i(\mathbb F_q\setminus\{c_i\})$, a set of size $(q-1)^m$, then the relaxation has a solution with $v\ne c$ with probability at most
--   $$E(D)=\sum_{d\in D\setminus\{0\}}\frac{q^{\dim (D^{*2})[Z(d)]}}{(q-1)^{\mathrm{wt}(d)}},$$
--   where $Z(d)$ is the zero set of $d$ and $W[S]$ the shortened code. Equivalently,
--   $$\#\{c' : c'_i\neq c_i\ \forall i,\ \exists\,(v,w)\text{ solving the relaxation with }v\neq c\}\ \le\ E(D)\,(q-1)^m .$$
--
--   This is the probabilistic heart of Lemma 7.3, stated independently of any machine model: an algorithm that solves the relaxation by Gaussian elimination and outputs $v$ when the solution is unique recovers the hidden codeword $c$ with probability at least $1-E(D)$.
--
--   **Formalization Note.** The count is `Nat.card` of the subtype of bad $c'$, and the probability bound is stated multiplied by $(q-1)^m$. The equation is written with pointwise operations on `Fin m → K`, with $a+a'$ and $a\odot a'$ replaced by $c+c'$ and $c\odot c'$, which they equal for every ordering of the pairs.
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held), §7.2, Lemma 7.3, p.39, and its proof, pp.39–40 (the relaxation w − (a+a′)⊙v + a⊙a′ = 0, Eq. (11), and the union bound over Δv ∈ C⊥∖{0}, Δw ∈ (C⊥)^{∗2}[Z(Δv)]).

import Mathlib
import Definitions.Def_TwoFoldOPI_schurFailureSum

namespace TwoFoldOPI

theorem relin_unique_solution_bound {K : Type*} [Field K] [Fintype K] [DecidableEq K] {m : ℕ}
    (D : Submodule K (Fin m → K)) (c : Fin m → K) (hc : c ∈ D) :
    (Nat.card {c' : Fin m → K // (∀ i, c' i ≠ c i) ∧
        ∃ v ∈ D, ∃ w ∈ schurSquare D, v ≠ c ∧ w - (c + c') * v + c * c' = 0} : ℝ) ≤
      schurFailureSum D * ((Fintype.card K : ℝ) - 1) ^ m := by sorry

end TwoFoldOPI
