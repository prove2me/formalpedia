-- Prove2me | Theorems.Thm_PetzMix_lemma_4_6
-- name    : PetzMix.lemma_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:15:51.502871+00:00
-- url     : https://prove2.me/theorems/daf811cb-fa1e-4a51-a0b8-26853f0974d7
-- title:
--   Lemma 4.6 — unitalized boundary approximants
-- statement:
--   Fix $d$ and $\beta$, and constants $c_0,C_Q,M_Q,\mu_Q$ with $C_Q,M_Q,\mu_Q>0$. There are constants $C_U,M_U,\mu_U>0$, independent of $n$ and $B$, such that the following holds. Let $H$ be in the family (1), let $B$ be a block, let $\tau_B$ be a full-rank state on $B$, and suppose Assumption 4.3 holds for $B$ with constants $c_0,C_Q,M_Q,\mu_Q$. Then there are operators $\hat Q_{B,r}$, $r=0,1,2,\dots$, such that for every $r$
--   $$
--   E_B\big(\hat Q_{B,r}^\dagger\hat Q_{B,r}\big)=I,
--   $$
--   $\operatorname{supp}\hat Q_{B,r}\subseteq N_{r+c_0}(\partial B)$, $\|\hat Q_{B,r}\|\le M_U$, and $\|\hat Q_{B,r}-Q_B\|\le C_Ue^{-\mu_Ur}$.
--
--   Exact normalization makes the approximating Heisenberg maps $A\mapsto E_B(\hat Q_{B,r}^\dagger A\hat Q_{B,r})$ unital, which is needed for Lipschitz-constant control.
--
--   Differences from the source:
--   - generalization: a fixed finite local dimension d → every d ≥ 1; reason: d = 1 is the trivial one-dimensional site; every d of the paper is included
--   - reading: two-site interactions h ∈ B(ℂ^d ⊗ ℂ^d) with ‖h‖ ≤ 1 → Hermitian bonds (IsPeriodicNN) with opNorm ≤ 1; reason: H is called a Hamiltonian and σ_β is a state only for Hermitian H
--   - encoding: the periodic chain Λn = ℤ/nℤ and operators on regions → sites Fin n, operators QDSGibbs.Op, region operators as A ⊗ I (SupportedOn); reason: Lean convention; same instances
--   - encoding: a block B = [a, b] ⊊ Λn → cycBlock ℓ a with 1 ≤ ℓ < n; reason: a nonempty proper cyclic interval is exactly such a block
--   - encoding: a full-rank state τ_B on B → T = τ_B ⊗ I_{B^c} with IsBlockRef B T (positive definite, trivial on B^c, ptr B T = 1); reason: the same objects, re-embedded on the full chain
--   - encoding: 'Suppose that Assumption … holds' with 'there exist constants' → the per-block predicates Asm43/Asm44 with their constants quantified before n, h and the block; reason: output constants independent of n and B, as the paper states
--   - generalization: c₀ > 0 in Assumption 4.3 → every c₀ : ℕ, including 0; reason: distances are integers, so N_{r+c₀} = N_{r+⌊c₀⌋}; c₀ = 0 is an additional instance
-- source:
--   Kim, Rapid mixing of quantum spin chains at any finite temperature, arXiv:2610.01190 (held copy sha256 38ff48d0…), Lemma 4.6, (68), p.22; Assumption 4.3, (60), p.20

import Mathlib
import Definitions.Def_PetzMix_petzAmp

open scoped Matrix ComplexOrder ENNReal

set_option autoImplicit false

namespace PetzMix

open QDSGibbs

/-- **Lemma 4.6 (Unitalized boundary approximants)** (Kim, Rapid mixing of quantum spin chains at any finite temperature, arXiv:2610.01190 (held copy sha256 38ff48d0…), Lemma 4.6, (68), p.22; Assumption 4.3,
(60), p.20). Fix `d` and `β`. For all constants `c₀, C_Q, M_Q, µ_Q` of Assumption 4.3 there are
constants `C_U, M_U, µ_U > 0`, independent of `n` and `B`, such that whenever Assumption 4.3 holds for
a block `B` (with these constants), there are operators `Q̂_{B,r}`, `r ≥ 0`, with
`E_B(Q̂_{B,r}† Q̂_{B,r}) = I`, `supp Q̂_{B,r} ⊆ N_{r+c₀}(∂B)`, `‖Q̂_{B,r}‖ ≤ M_U` and
`‖Q̂_{B,r} − Q_B‖ ≤ C_U e^{−µ_U r}`.

**Formalization Note** The block is `B = cycBlock ℓ a`, `1 ≤ ℓ < n`; `τ_B` is any full-rank state on
`B` (`T = τ_B ⊗ I`, `IsBlockRef B T`). The assumption is the per-block predicate `Asm43`, with its
constants quantified before the system. -/
theorem lemma_4_6 (d : ℕ) (hd : 1 ≤ d) (β : ℝ) (hβ : 0 ≤ β) (c₀ : ℕ) (CQ MQ μQ : ℝ)
    (hCQ : 0 < CQ) (hMQ : 0 < MQ) (hμQ : 0 < μQ) :
    ∃ CU MU μU : ℝ, 0 < CU ∧ 0 < MU ∧ 0 < μU ∧
      ∀ (n : ℕ) (h : Fin n → ChainOp n d), IsPeriodicNN h → (∀ i, opNorm (h i) ≤ 1) →
      ∀ (a : Fin n) (ℓ : ℕ), 1 ≤ ℓ → ℓ < n →
      ∀ T : ChainOp n d, IsBlockRef (cycBlock ℓ a) T →
      Asm43 (gibbs β (∑ i, h i)) (cycBlock ℓ a) T c₀ CQ MQ μQ →
      ∃ Qh : ℕ → ChainOp n d, ∀ r : ℕ,
        condExp (cycBlock ℓ a) T ((Qh r)ᴴ * Qh r) = 1 ∧
        SupportedOn (nbhd (r + c₀) (bdry (cycBlock ℓ a))) (Qh r) ∧
        opNorm (Qh r) ≤ MU ∧
        opNorm (Qh r - petzAmp (gibbs β (∑ i, h i)) (cycBlock ℓ a) T) ≤
          CU * Real.exp (-(μU * r)) := by sorry

end PetzMix
