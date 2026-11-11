-- Prove2me | Theorems.Thm_PetzMix_theorem_5_7
-- name    : PetzMix.theorem_5_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:16:56.804732+00:00
-- url     : https://prove2.me/theorems/a6310c64-6f72-4822-9a5e-ebf54a56d251
-- title:
--   Theorem 5.7 — proof of Assumption 4.4
-- statement:
--   Fix $d$ and $\beta\ge0$. There are constants $C_F,\mu_F>0$ such that for every Hamiltonian $H$ in the family (1) and every block $B$, with $\tau_B$ the Gibbs state of $H_B$, Assumption 4.4 holds for $B$ with constants $C_F,\mu_F$: for every decomposition $B=L,G_L,V,G_R,R$ into five consecutive intervals,
--   $$
--   \|(\tau_B)_{LRV}-(\tau_B)_{LR}\otimes(\tau_B)_V\|_1\le C_Fe^{-\mu_F\min\{|G_L|,|G_R|\}} .
--   $$
--
--   This discharges the second static assumption.
--
--   Differences from the source:
--   - generalization: a fixed finite local dimension d → every d ≥ 1; reason: d = 1 is the trivial one-dimensional site; every d of the paper is included
--   - reading: two-site interactions h ∈ B(ℂ^d ⊗ ℂ^d) with ‖h‖ ≤ 1 → Hermitian bonds (IsPeriodicNN) with opNorm ≤ 1; reason: H is called a Hamiltonian and σ_β is a state only for Hermitian H
--   - encoding: the periodic chain Λn = ℤ/nℤ and operators on regions → sites Fin n, operators QDSGibbs.Op, region operators as A ⊗ I (SupportedOn); reason: Lean convention; same instances
--   - encoding: a block B = [a, b] ⊊ Λn → cycBlock ℓ a with 1 ≤ ℓ < n; reason: a nonempty proper cyclic interval is exactly such a block
--   - encoding: constants depending only on β and d, independent of n → ∃ constants after (d, β), before n, h and the block; reason: the meaning of 'depending only on β and d'
--   - generalization: five consecutive intervals L, G_L, V, G_R, R → the five parts possibly empty (Asm44); reason: empty parts give trivial or |G| = 0 instances; the proof of Lemma 4.10 uses empty buffers (m = 0)
-- source:
--   Kim, Rapid mixing of quantum spin chains at any finite temperature, arXiv:2610.01190 (held copy sha256 38ff48d0…), Theorem 5.7, p.31

import Mathlib
import Definitions.Def_PetzMix_petzAmp

open scoped Matrix ComplexOrder ENNReal

set_option autoImplicit false

namespace PetzMix

open QDSGibbs

/-- **Theorem 5.7 (Proof of Assumption 4.4)** (Kim, Rapid mixing of quantum spin chains at any finite temperature, arXiv:2610.01190 (held copy sha256 38ff48d0…), Theorem 5.7, p.31). Assumption 4.4 holds for the
Hamiltonians in (1), with constants depending only on `β` and `d`, for `τ_B` the block Gibbs state of
(103).

**Formalization Note** The block is `cycBlock ℓ a`, `1 ≤ ℓ < n`; `T = τ_B ⊗ I` is `tauFull β h B`. -/
theorem theorem_5_7 (d : ℕ) (hd : 1 ≤ d) (β : ℝ) (hβ : 0 ≤ β) :
    ∃ CF μF : ℝ, 0 < CF ∧ 0 < μF ∧
      ∀ (n : ℕ) (h : Fin n → ChainOp n d), IsPeriodicNN h → (∀ i, opNorm (h i) ≤ 1) →
      ∀ (a : Fin n) (ℓ : ℕ), 1 ≤ ℓ → ℓ < n →
        Asm44 a ℓ (tauFull β h (cycBlock ℓ a)) CF μF := by sorry

end PetzMix
