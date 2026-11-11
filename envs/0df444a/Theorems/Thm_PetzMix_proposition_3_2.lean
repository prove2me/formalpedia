-- Prove2me | Theorems.Thm_PetzMix_proposition_3_2
-- name    : PetzMix.proposition_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:14:38.352664+00:00
-- url     : https://prove2.me/theorems/934c44e2-447f-442f-8e3c-a445f0455e4c
-- title:
--   Proposition 3.2 — Schrödinger picture of the influence decay function
-- statement:
--   Fix $1\le\ell<n$ and suppose that the block updates have exterior influence decay function $\eta$ (Definition 3.1). Let $B\in\mathcal B_{n,\ell}$, let $i$ be a site and let $X_i=X_i^\dagger$ satisfy $\operatorname{tr}_i[X_i]=0$.
--
--   1. If $i\in B$, then $\Phi_B(X_i)=0$.
--   2. If $i\notin B$, then
--   $$
--   \|\Phi_B(X_i)\|_{W_1}\le\big(1+\eta(\operatorname{dist}(i,B))\big)\|X_i\|_{W_1}.
--   $$
--
--   A block containing the anchor $i$ erases an $i$-anchored discrepancy, while a block missing $i$ enlarges it by at most the exterior influence at that distance.
--
--   **Formalization Note** $\operatorname{tr}_i[X]=0$ is `ptr {i} X = 0`; $\|\cdot\|_{W_1}$ is valued in $[0,\infty]$.
--
--   Differences from the source:
--   - generalization: a fixed finite local dimension d → every d ≥ 1; reason: d = 1 is the trivial one-dimensional site; every d of the paper is included
--   - reading: two-site interactions h ∈ B(ℂ^d ⊗ ℂ^d) with ‖h‖ ≤ 1 → Hermitian bonds (IsPeriodicNN) with opNorm ≤ 1; reason: H is called a Hamiltonian and σ_β is a state only for Hermitian H
--   - encoding: the periodic chain Λn = ℤ/nℤ and operators on regions → sites Fin n, operators QDSGibbs.Op, region operators as A ⊗ I (SupportedOn); reason: Lean convention; same instances
--   - encoding: B ∈ B_{n,ℓ}, the cyclic intervals of length ℓ, with 1 ≤ ℓ < n → cycBlock ℓ s for s : Fin n, 1 ≤ ℓ < n; reason: the n blocks are indexed by their left ends and are distinct for 1 ≤ ℓ < n
--   - reading: Definition 3.1 for every observable A → HasExtInfluence quantifies over Hermitian A; reason: the paper's usage: 'observable A = A†' (p.16); this weakens the hypothesis
-- source:
--   Kim, Rapid mixing of quantum spin chains at any finite temperature, arXiv:2610.01190 (held copy sha256 38ff48d0…), Proposition 3.2, (42), p.16; Definition 3.1, p.16

import Mathlib
import Definitions.Def_PetzMix_HasExtInfluence
import Definitions.Def_QDSGibbs_w1

open scoped Matrix ComplexOrder ENNReal

set_option autoImplicit false

namespace PetzMix

open QDSGibbs

/-- **Proposition 3.2 (Schrödinger picture of the influence decay function)** (Kim, Rapid mixing of quantum spin chains at any finite temperature, arXiv:2610.01190 (held copy sha256 38ff48d0…),
Proposition 3.2, (42), p.16; Definition 3.1, p.16). Suppose that the block updates have exterior
influence decay function `η`. Let `X_i = X_i†` satisfy `tr_i[X_i] = 0`. If `i ∈ B`, then
`Φ_B(X_i) = 0`. If `i ∉ B`, then `‖Φ_B(X_i)‖_{W1} ≤ (1 + η(dist(i, B))) ‖X_i‖_{W1}`.

**Formalization Note** `B = cycBlock ℓ s` ranges over `B_{n,ℓ}` with `1 ≤ ℓ < n` (p.16);
`tr_i[X] = 0` is `ptr {i} X = 0`. -/
theorem proposition_3_2 (n d : ℕ) (hd : 1 ≤ d) (β : ℝ) (hβ : 0 ≤ β) (h : Fin n → ChainOp n d)
    (hh : IsPeriodicNN h) (hnorm : ∀ i, opNorm (h i) ≤ 1) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (hℓn : ℓ < n)
    (η : ℕ → ℝ) (hη : HasExtInfluence β h ℓ η) (s i : Fin n) (X : ChainOp n d)
    (hX : X.IsHermitian) (hXi : ptr {i} X = 0) :
    (i ∈ cycBlock ℓ s → petzUpdate (gibbs β (∑ j, h j)) (cycBlock ℓ s) X = 0) ∧
    (i ∉ cycBlock ℓ s →
      w1 (petzUpdate (gibbs β (∑ j, h j)) (cycBlock ℓ s) X) ≤
        ENNReal.ofReal (1 + η (setDist i (cycBlock ℓ s))) * w1 X) := by sorry

end PetzMix
