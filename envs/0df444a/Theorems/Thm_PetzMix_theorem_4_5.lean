-- Prove2me | Theorems.Thm_PetzMix_theorem_4_5
-- name    : PetzMix.theorem_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:16:14.732623+00:00
-- url     : https://prove2.me/theorems/15464592-fe46-49c6-b973-85f6b024cae0
-- title:
--   Theorem 4.5 — Assumptions 4.3 and 4.4 imply exponentially decaying $\eta$
-- statement:
--   Fix $d$ and $\beta$, and constants $c_0$ and $C_Q,M_Q,\mu_Q,C_F,\mu_F>0$. There are constants $C_\eta,\xi>0$ such that the following holds. Let $H$ be in the family (1), $B$ a block and $\tau_B$ a full-rank state on $B$ for which Assumptions 4.3 and 4.4 hold with these constants. Then
--
--   1. for every site $i\notin B$ and every observable $A$,
--   $$
--   \delta_i\big(\Phi_B^\dagger(A)\big)\le\delta_i(A)+C_\eta e^{-\operatorname{dist}(i,B)/\xi}\|A\|_L ;
--   $$
--   2. for every site $i\in B$ and every operator $A$, $\delta_i(\Phi_B^\dagger(A))=0$.
--
--   With $\eta(r)=C_\eta e^{-r/\xi}$, this supplies the summable exterior influence decay function required by Theorem 3.4.
--
--   Differences from the source:
--   - generalization: a fixed finite local dimension d → every d ≥ 1; reason: d = 1 is the trivial one-dimensional site; every d of the paper is included
--   - reading: two-site interactions h ∈ B(ℂ^d ⊗ ℂ^d) with ‖h‖ ≤ 1 → Hermitian bonds (IsPeriodicNN) with opNorm ≤ 1; reason: H is called a Hamiltonian and σ_β is a state only for Hermitian H
--   - encoding: the periodic chain Λn = ℤ/nℤ and operators on regions → sites Fin n, operators QDSGibbs.Op, region operators as A ⊗ I (SupportedOn); reason: Lean convention; same instances
--   - encoding: a block B = [a, b] ⊊ Λn → cycBlock ℓ a with 1 ≤ ℓ < n; reason: a nonempty proper cyclic interval is exactly such a block
--   - encoding: a full-rank state τ_B on B → T = τ_B ⊗ I_{B^c} with IsBlockRef B T (positive definite, trivial on B^c, ptr B T = 1); reason: the same objects, re-embedded on the full chain
--   - encoding: 'Suppose that Assumption … holds' with 'there exist constants' → the per-block predicates Asm43/Asm44 with their constants quantified before n, h and the block; reason: output constants independent of n and B, as the paper states
--   - generalization: c₀ > 0 in Assumption 4.3 → every c₀ : ℕ, including 0; reason: distances are integers, so N_{r+c₀} = N_{r+⌊c₀⌋}; c₀ = 0 is an additional instance
--   - reading: observables A → Hermitian operators A; reason: the paper's usage: 'observable A = A†' (p.16)
--   - generalization: for i ∈ B, every observable A → every operator A; reason: Φ_B†(A) acts trivially on B for every A (Proposition 2.10)
-- source:
--   Kim, Rapid mixing of quantum spin chains at any finite temperature, arXiv:2610.01190 (held copy sha256 38ff48d0…), Theorem 4.5, (63), p.21

import Mathlib
import Definitions.Def_PetzMix_HasExtInfluence
import Definitions.Def_PetzMix_petzAmp

open scoped Matrix ComplexOrder ENNReal

set_option autoImplicit false

namespace PetzMix

open QDSGibbs

/-- **Theorem 4.5 (Assumptions 4.3 and 4.4 imply exponentially decaying `η`)** (Kim, Rapid mixing of quantum spin chains at any finite temperature, arXiv:2610.01190 (held copy sha256 38ff48d0…), Theorem 4.5,
(63), p.21). Fix `d` and `β`. For all constants of Assumptions 4.3 and 4.4 there are constants
`C_η, ξ > 0` such that, whenever both assumptions hold for a block `B`, for every site `i ∉ B` and
observable `A`, `δ_i(Φ_B†(A)) ≤ δ_i(A) + C_η e^{−dist(i,B)/ξ} ‖A‖_L`; and for `i ∈ B`,
`δ_i(Φ_B†(A)) = 0`.

**Formalization Note** The block is `B = cycBlock ℓ a`, `1 ≤ ℓ < n`; `τ_B` is any full-rank state on
`B` (`IsBlockRef B T`); the assumptions are the per-block predicates `Asm43`, `Asm44`, with constants
quantified before the system. Observables in the first clause are Hermitian; the second clause holds
for every operator. -/
theorem theorem_4_5 (d : ℕ) (hd : 1 ≤ d) (β : ℝ) (hβ : 0 ≤ β) (c₀ : ℕ) (CQ MQ μQ CF μF : ℝ)
    (hCQ : 0 < CQ) (hMQ : 0 < MQ) (hμQ : 0 < μQ) (hCF : 0 < CF) (hμF : 0 < μF) :
    ∃ Cη ξ : ℝ, 0 < Cη ∧ 0 < ξ ∧
      ∀ (n : ℕ) (h : Fin n → ChainOp n d), IsPeriodicNN h → (∀ i, opNorm (h i) ≤ 1) →
      ∀ (a : Fin n) (ℓ : ℕ), 1 ≤ ℓ → ℓ < n →
      ∀ T : ChainOp n d, IsBlockRef (cycBlock ℓ a) T →
      Asm43 (gibbs β (∑ i, h i)) (cycBlock ℓ a) T c₀ CQ MQ μQ → Asm44 a ℓ T CF μF →
      (∀ i : Fin n, i ∉ cycBlock ℓ a → ∀ A : ChainOp n d, A.IsHermitian →
        osc i (heisAdj (petzUpdate (gibbs β (∑ j, h j)) (cycBlock ℓ a)) A) ≤
          osc i A + Cη * Real.exp (-((setDist i (cycBlock ℓ a) : ℝ) / ξ)) * lip A) ∧
      (∀ i : Fin n, i ∈ cycBlock ℓ a → ∀ A : ChainOp n d,
        osc i (heisAdj (petzUpdate (gibbs β (∑ j, h j)) (cycBlock ℓ a)) A) = 0) := by sorry

end PetzMix
