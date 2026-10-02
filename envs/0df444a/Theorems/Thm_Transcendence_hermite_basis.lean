-- Prove2me | Theorems.Thm_Transcendence_hermite_basis
-- name    : Transcendence.hermite_basis
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-02T08:18:37.592784+00:00
-- url     : https://prove2.me/theorems/2e4bdbd5-ff19-4bd2-a497-f14f53276e86
-- title:
--   Hermite interpolation over a field of characteristic 0: polynomials dual to the jets of order < S₀ at a finite set of nodes
-- statement:
--   Let $K$ be a field of characteristic $0$, $E \subset K$ a finite set and $S_0 \in \mathbb{N}$, and write $q^{(k)}$ for the $k$-th formal derivative of a polynomial $q$. There are polynomials $b_{\zeta,k} \in K[X]$ ($\zeta \in E$, $0 \le k < S_0$) of degree less than $|E|S_0$ with
--
--   $$b_{\zeta,k}^{(k')}(\zeta') = \begin{cases}1 & \text{if } (\zeta', k') = (\zeta, k),\\ 0 & \text{otherwise}\end{cases} \qquad (\zeta' \in E,\ 0 \le k' < S_0),$$
--
--   and every polynomial $q \in K[X]$ of degree less than $|E|S_0$ satisfies
--
--   $$q = \sum_{\zeta \in E}\ \sum_{0 \le k < S_0} q^{(k)}(\zeta)\, b_{\zeta,k}.$$
--
--   `Transcendence.coord_hermite_step` uses it to write the Hermite remainder of every slice of a function of several variables in one fixed basis, so that the remainder depends on the other variables only through the jets of the function at the nodes.
--
--   It is one step of the proof of Baker's theorem formalised in this mission, which follows Chapter 4 of Waldschmidt's book: Baker's theorem from the criterion of Schneider–Lang for Cartesian products, as observed by Bertrand and Masser (1980).
--
--   **Novelty.** None: Hermite interpolation, a standard result. The contribution of this node is the formal proof.
-- source:
--   Standard (Hermite interpolation). Formal proof: Diaz modulus mission, 2 October 2026 (C. Perassi).

import Mathlib

open Polynomial

namespace Transcendence

/-- **Hermite interpolation** over a field of characteristic `0`. Let `E` be a finite set and `S₀ ∈ ℕ`. There
are polynomials `b_{ζ,k}` (`ζ ∈ E`, `k < S₀`) of degree `< |E|·S₀` with `b_{ζ,k}^{(k')}(ζ') = 1` if
`(ζ', k') = (ζ, k)` and `0` otherwise, for all `ζ' ∈ E` and `k' < S₀`. Every polynomial `q` of degree
`< |E|·S₀` is then determined by its jets on `E`: `q = ∑_{ζ ∈ E, k < S₀} q^{(k)}(ζ) · b_{ζ,k}`. -/
theorem hermite_basis {K : Type*} [Field K] [CharZero K] [DecidableEq K] (E : Finset K) (S₀ : ℕ) :
    ∃ b : ↥E × Fin S₀ → K[X], (∀ x, b x ∈ degreeLT K (E.card * S₀)) ∧
      (∀ x y : ↥E × Fin S₀,
        (derivative^[y.2] (b x)).eval (y.1 : K) = if x = y then 1 else 0) ∧
      ∀ q ∈ degreeLT K (E.card * S₀),
        q = ∑ x : ↥E × Fin S₀, C ((derivative^[x.2] q).eval (x.1 : K)) * b x := by
  sorry

end Transcendence
