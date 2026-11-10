-- Prove2me | Theorems.Thm_QThermalClassical_lemma_14
-- name    : QThermalClassical.lemma_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:14:44.407206+00:00
-- url     : https://prove2.me/theorems/c3dfa765-f77c-4e0f-b684-594dc909c73e
-- title:
--   Lemma 14 — pinning procedure: separability for $\beta\le1/(12v)$
-- statement:
--   Let $H=\sum_a\lambda_aP_a$ be a Pauli Hamiltonian, $v>0$ and $0\le\beta\le1/(12v)$. Suppose that for every set of sites $S$ with $A(S)\neq\emptyset$ and every term $a^*\in A$ with $a^*\cap S\neq\emptyset$ there is a sampling procedure returning coefficients $b$ and Paulis $E$ with
--   $$
--   \mathbb E[I+bE]=e^{-\eta H(S)}e^{\eta\left(H(S)-H^{(S)}_{(a^*)}\right)},\qquad \eta=\beta/2\qquad(102),
--   $$
--   where $E$ is a Pauli product (up to a phase) of an ordered list $C(E)$ of terms from $A(S)$, of order $t=|C(E)|\ge1$, and $|b|\le(\beta v/2)^t$. Then the Gibbs state $\rho_\beta(H)$ is separable.
--
--   With Lemma 9 ($v=6ks$) this gives clause 1 of Theorem 1(a).
--
--   Differences from the source:
--   - reading: a sampling procedure and its expectation $\mathbb E$ → a sampler with block-wise expectation; reason: every countable distribution is a sampler with one outcome per block, and for $\beta\le1/(12v)$ the bound makes the expectation absolutely convergent
--   - generalization: a sampling procedure for every set of sites $S$ → only for $S$ with $A(S)\neq\emptyset$; reason: Algorithm 1 calls the primitive only while $A(S)\neq\emptyset$; at $A(S)=\emptyset$ no outcome with $|C(E)|\ge1$ and $C(E)\subseteq A(S)$ exists, so the printed quantifier would make the lemma vacuous
--   - reading: $\eta$ in (102) → $\eta=\beta/2$; reason: lines 8–9 of Algorithm 1 ($\eta\to\beta/2$) and the proof (104)–(105), which evaluates $L(\beta/2)$
--   - reading: the order $t=|C(E)|$ → $t\ge1$; reason: Lemma 9 defines the order with $t_i=|C(E_i)|\ge1$, and (104) uses $(\eta v)^t\le(\eta v/q)q^t$, false at $t=0$
--   - reading: Paulis $E$ constructed from $C(E)$ → a Pauli product up to a phase $\omega\in\{\pm1,\pm i\}$ of a reordering of $C(E)$; reason: the form of Lemma 9's outcomes
--   - reading: $\beta\le1/(12v)$ → $0\le\beta\le1/(12v)$ with $v>0$; reason: $\beta$ is an inverse temperature (eqs. (9), (22)) and $1/(12v)$ presumes $v>0$
--   - encoding: the Gibbs state $e^{-\beta H}$ is separable → the normalized Gibbs state $\rho_\beta(H)$ lies in $\mathrm{Sep}_n$; reason: they differ by a positive factor (p.19)
--   - encoding: a Pauli Hamiltonian $H=\sum_{a\in A}c_aP_a$ with distinct non-identity Pauli strings → a coefficient function $c$ on Pauli words with $c(I)=0$, $A=\{P: c_P\neq 0\}$; reason: distinctness is automatic and words with coefficient $0$ change neither $H$ nor any condition; no instance changes
-- source:
--   J. Cotler, H. Putterman, A. Zlokapa, When quantum thermal states look classical, arXiv:2607.28536 (held version, sha256 7491d0b2…), Lemma 14, eq. (102), p.32; Algorithm 1, p.27

import Mathlib
import Definitions.Def_QThermalClassical_ham
import Definitions.Def_QThermalClassical_gibbs
import Definitions.Def_QThermalClassical_IsSeparable
import Definitions.Def_QThermalClassical_restrictTouching
import Definitions.Def_QThermalClassical_propagator
import Definitions.Def_QThermalClassical_IsPauliProd
import Definitions.Def_QThermalClassical_Sampler
import Definitions.Def_QThermalClassical_Config

set_option autoImplicit false

namespace QThermalClassical

/-- **Lemma 14 (Pinning procedure).** Let `H = Σ_P c_P P` be a Pauli Hamiltonian and `v > 0`.
Suppose that for every set of sites `S` (at which the loop of Algorithm 1 runs, `A(S) ≠ ∅`)
and every term `a* ∈ A` with `a* ∩ S ≠ ∅` there is a sampling procedure returning
coefficients `b` and Paulis `E` with `𝔼[I + bE] = e^{−ηH(S)} e^{η(H(S) − H^{(S)}_{(a*)})}` (102),
`η = β/2`, where `E` is constructed from an ordered list `C(E)` of terms from `A(S)`, the order
of `E` is `t = |C(E)| ≥ 1`, and `|b| ≤ (βv/2)^t`. Then the Gibbs state is separable for
`0 ≤ β ≤ 1/(12v)`.

Source: J. Cotler, H. Putterman, A. Zlokapa, *When quantum thermal states look classical*,
arXiv:2607.28536 (held version, sha256 7491d0b2…), Lemma 14, eq. (102), p.32; Algorithm 1, p.27.

**Formalization Note.** The sampling procedure is a `Sampler` and `𝔼` its block-by-block
expectation; every countable distribution is a `Sampler` with one outcome per block, and in
this range of `β` the bound makes its expectation absolutely convergent. "Separable" is `ρ_β ∈ Sep_n` for the normalized Gibbs
state (the paper works with `e^{−βH}`, which differs by a positive factor). The sampler is
required only at the sites `S` where Algorithm 1 calls it (`A(S) ≠ ∅`); at `A(S) = ∅` a
sampler with `|C(E)| ≥ 1` and `C(E) ⊆ A(S)` cannot exist. `η = β/2` as in lines 8–9 of
Algorithm 1. `β ≥ 0` is the range of inverse temperatures of (9) and (22). -/
theorem lemma_14 {Q : Type} [Fintype Q] [DecidableEq Q] (c : PauliWord Q → ℝ)
    (hc0 : c (fun _ => 0) = 0) (v β : ℝ) (hv : 0 < v) (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / (12 * v))
    (hsamp : ∀ S : Finset Q, (termsIn c S).Nonempty → ∀ a : PauliWord Q, c a ≠ 0 →
      (pauliSupport a ∩ S).Nonempty →
      ∃ σ : Sampler Q,
        (∀ t j, IsPauliProd (σ.o t j).C (σ.o t j).E ∧ (∀ b ∈ (σ.o t j).C, b ∈ termsIn c S) ∧
          1 ≤ (σ.o t j).C.length ∧ |(σ.o t j).b| ≤ (β * v / 2) ^ (σ.o t j).C.length) ∧
        σ.HasExpect (fun o => 1 + ((o.b : ℝ) : ℂ) • o.E)
          (propagator (ham (restrictIn c S)) (ham (restrictTouching c S (pauliSupport a)))
            (β / 2))) :
    IsSeparable (gibbs (ham c) β) := by sorry

end QThermalClassical
