-- Prove2me | Theorems.Thm_PetzMix_lemma_5_2
-- name    : PetzMix.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:16:35.18147+00:00
-- url     : https://prove2.me/theorems/3578088e-7898-434c-9a24-8e0e3ddec5fa
-- title:
--   Lemma 5.2 — uniform bound on $F_B(1+it)$
-- statement:
--   Fix $d$ and $\beta\ge0$. There is a constant $M\ge1$ such that for every Hamiltonian $H$ in the family (1), every block $B$ and every $t\in\mathbb R$,
--   $$
--   \|F_B(1+it)\|\le M ,
--   $$
--   where $F_B(z)=\sigma_\beta^z(\tau_B^{-z}\otimes\sigma_{\beta,B^c}^{-z})$ and $\tau_B$ is the Gibbs state of $H_B$.
--
--   This is the estimate on the line $\operatorname{Re}z=1$ of the complex interpolation.
--
--   Differences from the source:
--   - generalization: a fixed finite local dimension d → every d ≥ 1; reason: d = 1 is the trivial one-dimensional site; every d of the paper is included
--   - reading: two-site interactions h ∈ B(ℂ^d ⊗ ℂ^d) with ‖h‖ ≤ 1 → Hermitian bonds (IsPeriodicNN) with opNorm ≤ 1; reason: H is called a Hamiltonian and σ_β is a state only for Hermitian H
--   - encoding: the periodic chain Λn = ℤ/nℤ and operators on regions → sites Fin n, operators QDSGibbs.Op, region operators as A ⊗ I (SupportedOn); reason: Lean convention; same instances
--   - encoding: a block B = [a, b] ⊊ Λn → cycBlock ℓ a with 1 ≤ ℓ < n; reason: a nonempty proper cyclic interval is exactly such a block
--   - encoding: constants depending only on β and d, independent of n → ∃ constants after (d, β), before n, h and the block; reason: the meaning of 'depending only on β and d'
-- source:
--   Kim, Rapid mixing of quantum spin chains at any finite temperature, arXiv:2610.01190 (held copy sha256 38ff48d0…), Lemma 5.2, (107), p.29

import Mathlib
import Definitions.Def_PetzMix_petzAmp

open scoped Matrix ComplexOrder ENNReal

set_option autoImplicit false

namespace PetzMix

open QDSGibbs

/-- **Lemma 5.2 (Uniform bound at `Re z = 1`)** (Kim, Rapid mixing of quantum spin chains at any finite temperature, arXiv:2610.01190 (held copy sha256 38ff48d0…), Lemma 5.2, (107), p.29). Fix `d` and `β`.
There exists a constant `M ≥ 1` such that for every Hamiltonian of the family (1), every block `B`
and every `t ∈ ℝ`, `‖F_B(1 + it)‖ ≤ M`.

**Formalization Note** `M` depends on `β` and `d` only (§5 Setup, p.28); the block is `cycBlock ℓ a`,
`1 ≤ ℓ < n`. -/
theorem lemma_5_2 (d : ℕ) (hd : 1 ≤ d) (β : ℝ) (hβ : 0 ≤ β) :
    ∃ M : ℝ, 1 ≤ M ∧
      ∀ (n : ℕ) (h : Fin n → ChainOp n d), IsPeriodicNN h → (∀ i, opNorm (h i) ≤ 1) →
      ∀ (a : Fin n) (ℓ : ℕ), 1 ≤ ℓ → ℓ < n → ∀ t : ℝ,
        opNorm (FB β h (cycBlock ℓ a) (1 + Complex.I * t)) ≤ M := by sorry

end PetzMix
