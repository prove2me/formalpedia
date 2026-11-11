-- Prove2me | Theorems.Thm_PetzMix_theorem_5_3
-- name    : PetzMix.theorem_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:16:34.432801+00:00
-- url     : https://prove2.me/theorems/0e6355e8-7583-4c5b-b560-156f8e59cfb2
-- title:
--   Theorem 5.3 — proof of Assumption 4.3
-- statement:
--   Fix $d$ and $\beta\ge0$. There are constants $c_0$ (a positive integer) and $C_Q,M_Q,\mu_Q>0$ such that for every Hamiltonian $H$ in the family (1) and every block $B$, with $\tau_B$ the Gibbs state of $H_B$, Assumption 4.3 holds for $B$ with these constants. In particular one may take
--   $$
--   \tilde Q_{B,r}=D_{S_r^c}(Q_B),\qquad S_r=N_{r+c_0}(\partial B):
--   $$
--   for every integer $r\ge0$, $D_{S_r^c}(Q_B)$ is supported on $S_r$, $\|Q_B-D_{S_r^c}(Q_B)\|\le C_Qe^{-\mu_Qr}$ and $\|Q_B\|+\|D_{S_r^c}(Q_B)\|\le M_Q$.
--
--   This discharges the first static assumption for all one-dimensional nearest-neighbour Gibbs states at every finite temperature.
--
--   Differences from the source:
--   - generalization: a fixed finite local dimension d → every d ≥ 1; reason: d = 1 is the trivial one-dimensional site; every d of the paper is included
--   - reading: two-site interactions h ∈ B(ℂ^d ⊗ ℂ^d) with ‖h‖ ≤ 1 → Hermitian bonds (IsPeriodicNN) with opNorm ≤ 1; reason: H is called a Hamiltonian and σ_β is a state only for Hermitian H
--   - encoding: the periodic chain Λn = ℤ/nℤ and operators on regions → sites Fin n, operators QDSGibbs.Op, region operators as A ⊗ I (SupportedOn); reason: Lean convention; same instances
--   - encoding: a block B = [a, b] ⊊ Λn → cycBlock ℓ a with 1 ≤ ℓ < n; reason: a nonempty proper cyclic interval is exactly such a block
--   - encoding: constants depending only on β and d, independent of n → ∃ constants after (d, β), before n, h and the block; reason: the meaning of 'depending only on β and d'
-- source:
--   Kim, Rapid mixing of quantum spin chains at any finite temperature, arXiv:2610.01190 (held copy sha256 38ff48d0…), Theorem 5.3, p.30

import Mathlib
import Definitions.Def_PetzMix_petzAmp
import Definitions.Def_QDSGibbs_cov

open scoped Matrix ComplexOrder ENNReal

set_option autoImplicit false

namespace PetzMix

open QDSGibbs

/-- **Theorem 5.3 (Proof of Assumption 4.3)** (Kim, Rapid mixing of quantum spin chains at any finite temperature, arXiv:2610.01190 (held copy sha256 38ff48d0…), Theorem 5.3, p.30). Assumption 4.3 holds for the
Hamiltonians in (1), with constants depending only on `β` and `d`, for `τ_B` the block Gibbs state of
(103). In particular one may take `Q̃_{B,r} = D_{S_r^c}(Q_B)`, obtained by depolarizing outside
`S_r = N_{r+c₀}(∂B)`.

**Formalization Note** The block is `cycBlock ℓ a`, `1 ≤ ℓ < n`; `T = τ_B ⊗ I` is `tauFull β h B`;
`D_{S_r^c}` is the public `marg S_r`. The second clause, with the explicit approximant, implies the
first. -/
theorem theorem_5_3 (d : ℕ) (hd : 1 ≤ d) (β : ℝ) (hβ : 0 ≤ β) :
    ∃ c₀ : ℕ, 0 < c₀ ∧ ∃ CQ MQ μQ : ℝ, 0 < CQ ∧ 0 < MQ ∧ 0 < μQ ∧
      ∀ (n : ℕ) (h : Fin n → ChainOp n d), IsPeriodicNN h → (∀ i, opNorm (h i) ≤ 1) →
      ∀ (a : Fin n) (ℓ : ℕ), 1 ≤ ℓ → ℓ < n →
        Asm43 (gibbs β (∑ i, h i)) (cycBlock ℓ a) (tauFull β h (cycBlock ℓ a)) c₀ CQ MQ μQ ∧
        ∀ r : ℕ,
          SupportedOn (nbhd (r + c₀) (bdry (cycBlock ℓ a)))
              (marg (nbhd (r + c₀) (bdry (cycBlock ℓ a)))
                (petzAmp (gibbs β (∑ i, h i)) (cycBlock ℓ a) (tauFull β h (cycBlock ℓ a)))) ∧
          opNorm (petzAmp (gibbs β (∑ i, h i)) (cycBlock ℓ a) (tauFull β h (cycBlock ℓ a)) -
              marg (nbhd (r + c₀) (bdry (cycBlock ℓ a)))
                (petzAmp (gibbs β (∑ i, h i)) (cycBlock ℓ a) (tauFull β h (cycBlock ℓ a)))) ≤
            CQ * Real.exp (-(μQ * r)) ∧
          opNorm (petzAmp (gibbs β (∑ i, h i)) (cycBlock ℓ a) (tauFull β h (cycBlock ℓ a))) +
              opNorm (marg (nbhd (r + c₀) (bdry (cycBlock ℓ a)))
                (petzAmp (gibbs β (∑ i, h i)) (cycBlock ℓ a) (tauFull β h (cycBlock ℓ a)))) ≤
            MQ := by sorry

end PetzMix
