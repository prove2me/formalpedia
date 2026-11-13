-- Prove2me | Theorems.Thm_StateSynthNP_derandomize_coherently
-- name    : StateSynthNP.derandomize_coherently
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:49:12.039614+00:00
-- url     : https://prove2.me/theorems/cf470b96-f231-42a6-b174-3ce24f017903
-- title:
--   Coherent removal of the random bits: $\langle 0^m\otimes\varphi,\,w\rangle=2^{-m}\sum_r\langle\varphi,v_r\rangle$
-- statement:
--   Let $m\in\mathbb N$, let $v_r$ ($r\in\{0,1\}^m$) and $\varphi$ be unit vectors of $\mathbb C^{\iota}$, and let $w=(H^{\otimes m}\otimes I)\bigl(2^{-m/2}\sum_r|r\rangle\otimes v_r\bigr)$ be the state obtained by preparing $v_r$ in superposition over the random strings and then applying $H^{\otimes m}$ to the random register. Then
--
--   1. $$
--   \bigl\langle\,|0^m\rangle\otimes\varphi,\ w\,\bigr\rangle=2^{-m}\sum_{r\in\{0,1\}^m}\langle\varphi,v_r\rangle ;
--   $$
--   2. if $\delta\ge0$, $\operatorname{Re}\langle\varphi,v_r\rangle\ge1-\delta$ for every $r$ outside a set of at most $\eta\,2^m$ strings, and $1-\delta-2\eta\ge0$, then
--   $$
--   \bigl|\bigl\langle\,|0^m\rangle\otimes\varphi,\ w\,\bigr\rangle\bigr|^2\ge(1-\delta-2\eta)^2 .
--   $$
--
--   This is the "standard argument" that turns a randomized preparation, good except with probability $\eta$ over the random bits, into a deterministic one: the random register is returned to $|0^m\rangle$ and the fidelity loss is controlled. The hypothesis on the real part of $\langle\varphi,v_r\rangle$ is the paper's "with the same global phase"; a hypothesis on $|\langle\varphi,v_r\rangle|$ alone would not suffice, since the phases of the $v_r$ could cancel.
--
--   Differences from the source:
--
--   - reading: by a standard argument … prepare |ψ̂⟩ (with the same global phase) in superposition over all choices of random bits, and then cleanly uncompute them … to deterministically obtain |ψ̂⟩ → the identity ⟨0^m ⊗ φ, w⟩ = 2^{−m} Σ_r ⟨φ, v_r⟩ and the bound |⟨0^m ⊗ φ, w⟩|² ≥ (1 − δ − 2η)² under Re⟨φ, v_r⟩ ≥ 1 − δ outside a set of at most η 2^m strings; reason: this is the standard argument with explicit constants; "the same global phase" is the hypothesis on the real part
--   - encoding: an error parameter → δ ≥ 0; reason: excludes only negative errors, which are meaningless
-- source:
--   A. Sen, State Synthesis with an NP oracle, arXiv:2611.02370 (held version, sha256 1705b965726e24478266bc8bdb695f0c6c6e06e172eff71c247272c116f264d0), proof of Lemma 2.2, p.5 ("by a standard argument, we can prepare |ψ̂⟩ (with the same global phase) in superposition over all choices of poly(n, log(1/ε)) size random bits, and then cleanly uncompute them at the end, along with rescaling ε, to deterministically obtain |ψ̂⟩ such that |⟨ψ̂|ψ⟩|² ≥ 1 − ε")

import Mathlib
import Definitions.Def_StateSynthNP_randRegisterState

set_option autoImplicit false

namespace StateSynthNP

/-- **Coherent removal of the random bits.** "Thus, except with probability ε over the random bits,
|⟨ψ̂|ψ⟩|² ≥ 1 − O(ε). So, by a standard argument, we can prepare |ψ̂⟩ (with the same global phase) in
superposition over all choices of poly(n, log(1/ε)) size random bits, and then cleanly uncompute them
at the end, along with rescaling ε, to deterministically obtain |ψ̂⟩ such that |⟨ψ̂|ψ⟩|² ≥ 1 − ε."

Source: A. Sen, *State Synthesis with an NP oracle*, arXiv:2611.02370 (held version, sha256 1705b965…), proof of Lemma 2.2, p.5.

Statement: let `v_r` (`r ∈ {0,1}^m`) and `φ` be unit vectors of `ℂ^ι` and
`w = (H^{⊗m} ⊗ I)(2^{−m/2} Σ_r |r⟩ ⊗ v_r)`. Then
1. `⟨|0^m⟩ ⊗ φ, w⟩ = 2^{−m} Σ_r ⟨φ, v_r⟩`;
2. if `δ ≥ 0`, `Re⟨φ, v_r⟩ ≥ 1 − δ` for every `r` outside a set of at most `η 2^m` strings, and
   `1 − δ − 2η ≥ 0`, then `|⟨|0^m⟩ ⊗ φ, w⟩|² ≥ (1 − δ − 2η)²`.

**Formalization Note.** "With the same global phase" is the hypothesis on `Re⟨φ, v_r⟩` (not on
`|⟨φ, v_r⟩|`, under which the phases of the `v_r` could cancel). The inner product is
`⟨a, b⟩ = Σ_i conj(a_i) b_i`. -/
theorem derandomize_coherently {ι : Type} [Fintype ι] (m : ℕ) (v : (Fin m → Bool) → ι → ℂ)
    (φ : ι → ℂ) (hv : ∀ r, ∑ i, Complex.normSq (v r i) = 1)
    (hφ : ∑ i, Complex.normSq (φ i) = 1) :
    (∑ i, star (φ i) * randRegisterState m v (fun _ => false, i)) =
        ((2 : ℂ) ^ m)⁻¹ * ∑ r, ∑ i, star (φ i) * v r i ∧
    ∀ (δ η : ℝ) (Bad : Finset (Fin m → Bool)), 0 ≤ δ → (Bad.card : ℝ) ≤ η * 2 ^ m →
      (∀ r, r ∉ Bad → 1 - δ ≤ (∑ i, star (φ i) * v r i).re) → 0 ≤ 1 - δ - 2 * η →
      (1 - δ - 2 * η) ^ 2 ≤
        Complex.normSq (∑ i, star (φ i) * randRegisterState m v (fun _ => false, i)) := by sorry

end StateSynthNP
