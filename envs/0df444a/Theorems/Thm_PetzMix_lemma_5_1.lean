-- Prove2me | Theorems.Thm_PetzMix_lemma_5_1
-- name    : PetzMix.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:16:46.68389+00:00
-- url     : https://prove2.me/theorems/eb701735-e910-4bc5-9dad-9225937c6839
-- title:
--   Lemma 5.1 — boundary locality of $F_B(it)$
-- statement:
--   Fix $d$ and $\beta\ge0$. There are constants $c_0,C,\nu,v>0$ (with $c_0$ an integer) such that for every Hamiltonian $H$ in the family (1), every block $B$, every integer $r\ge0$ and every $t\in\mathbb R$,
--   $$
--   \big\|F_B(it)-D_{S_r^c}\big(F_B(it)\big)\big\|\le Ce^{-\nu r+v|t|},\qquad S_r=N_{r+c_0}(\partial B),
--   $$
--   where $F_B(z)=\sigma_\beta^z(\tau_B^{-z}\otimes\sigma_{\beta,B^c}^{-z})$, $\tau_B$ is the Gibbs state of $H_B$, and $D_{S_r^c}(X)=\operatorname{tr}_{S_r^c}(X)\otimes I_{S_r^c}/d^{|S_r^c|}$ depolarizes every site outside $S_r$.
--
--   This is the estimate on the line $\operatorname{Re}z=0$ of the complex interpolation that proves Assumption 4.3.
--
--   **Formalization Note** $D_{S^c}$ is the public normalized full-space marginal `marg S`.
--
--   Differences from the source:
--   - generalization: a fixed finite local dimension d → every d ≥ 1; reason: d = 1 is the trivial one-dimensional site; every d of the paper is included
--   - reading: two-site interactions h ∈ B(ℂ^d ⊗ ℂ^d) with ‖h‖ ≤ 1 → Hermitian bonds (IsPeriodicNN) with opNorm ≤ 1; reason: H is called a Hamiltonian and σ_β is a state only for Hermitian H
--   - encoding: the periodic chain Λn = ℤ/nℤ and operators on regions → sites Fin n, operators QDSGibbs.Op, region operators as A ⊗ I (SupportedOn); reason: Lean convention; same instances
--   - encoding: a block B = [a, b] ⊊ Λn → cycBlock ℓ a with 1 ≤ ℓ < n; reason: a nonempty proper cyclic interval is exactly such a block
--   - encoding: constants depending only on β and d, independent of n → ∃ constants after (d, β), before n, h and the block; reason: the meaning of 'depending only on β and d'
-- source:
--   Kim, Rapid mixing of quantum spin chains at any finite temperature, arXiv:2610.01190 (held copy sha256 38ff48d0…), Lemma 5.1, (106), p.29; (104), p.29; (142), p.45

import Mathlib
import Definitions.Def_PetzMix_petzAmp

open scoped Matrix ComplexOrder ENNReal

set_option autoImplicit false

namespace PetzMix

open QDSGibbs

/-- **Lemma 5.1 (Boundary locality at `Re z = 0`)** (Kim, Rapid mixing of quantum spin chains at any finite temperature, arXiv:2610.01190 (held copy sha256 38ff48d0…), Lemma 5.1, (106), p.29; (104), p.29;
`S_r`, `D_{S_r^c}` in (142), p.45). Fix `d` and `β`. There exist constants `c₀, C, ν, v > 0` such
that for every Hamiltonian of the family (1), every block `B`, every integer `r ≥ 0` and every
`t ∈ ℝ`, `‖F_B(it) − D_{S_r^c}(F_B(it))‖ ≤ C e^{−νr + v|t|}`, with `S_r = N_{r+c₀}(∂B)`.

**Formalization Note** Constants may depend on `β` and `d` only (§5 Setup, p.28). `D_{S^c}`,
depolarizing every site outside `S`, is the public `marg S`. `F_B` is `FB`; the block is
`cycBlock ℓ a`, `1 ≤ ℓ < n`. -/
theorem lemma_5_1 (d : ℕ) (hd : 1 ≤ d) (β : ℝ) (hβ : 0 ≤ β) :
    ∃ c₀ : ℕ, 0 < c₀ ∧ ∃ C ν v : ℝ, 0 < C ∧ 0 < ν ∧ 0 < v ∧
      ∀ (n : ℕ) (h : Fin n → ChainOp n d), IsPeriodicNN h → (∀ i, opNorm (h i) ≤ 1) →
      ∀ (a : Fin n) (ℓ : ℕ), 1 ≤ ℓ → ℓ < n → ∀ (r : ℕ) (t : ℝ),
        opNorm (FB β h (cycBlock ℓ a) (Complex.I * t) -
            marg (nbhd (r + c₀) (bdry (cycBlock ℓ a))) (FB β h (cycBlock ℓ a) (Complex.I * t))) ≤
          C * Real.exp (-(ν * r) + v * |t|) := by sorry

end PetzMix
