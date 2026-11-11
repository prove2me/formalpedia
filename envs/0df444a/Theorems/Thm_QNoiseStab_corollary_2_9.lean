-- Prove2me | Theorems.Thm_QNoiseStab_corollary_2_9
-- name    : QNoiseStab.corollary_2_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:22:58.140319+00:00
-- url     : https://prove2.me/theorems/676330cf-55bc-4e3a-9fba-45c0673866be
-- title:
--   Corollary 2.9 — after $t$ queries the input register has Fourier degree at most $t$
-- statement:
--   Work over the domain $X=\mathbb Z_d$ with a uniformly random input. Let $\mathcal A$ be any $T$-query algorithm with phase queries $O|i,p,w\rangle|x\rangle=\omega^{p x_i}|i,p,w\rangle|x\rangle$, where $\omega^d=1$, and let $|\psi_t^x\rangle$ be its state after $t\le T$ queries on input $x$. Then the purified state $\sum_x d^{-n/2}|\psi_t^x\rangle|x\rangle$ is a linear combination of states $|q\rangle|\hat z\rangle$ whose input register is a Fourier basis state $|\hat z\rangle$ with at most $t$ nonzero entries. Equivalently, for every computational-basis state $q$ of the registers $QPW$ and every $z\in\mathbb Z_d^n$ with $|\mathrm{Supp}'(z)|>t$,
--
--   $$
--   \sum_{x\in\mathbb Z_d^n}\overline{\langle x|\hat z\rangle}\;\langle q|\psi_t^x\rangle=0 .
--   $$
--
--   This is the structural input of Theorem 3.5: the state of every branch of the measured algorithm registers lies in $B_T$.
--
--   **Formalization Note** The Fourier basis uses the primitive root $e^{2\pi i/d}$; the oracle root $\omega$ is any $d$-th root of unity. The algorithm is the published `QAlgorithms.QueryAlg` with an arbitrary finite workspace.
--
--   Differences from the source:
--   - encoding: "a linear combination of states whose input register in the Fourier basis $|\hat z\rangle$ has … at most $t$ non-0 entries" → every Fourier coefficient $\sum_x\overline{\hat z(x)}\,\psi_t^x(q)$ with $|\mathrm{Supp}'(z)|>t$ vanishes, for every basis state $q$ of $QPW$; reason: the coefficient of $|q\rangle|\hat z\rangle$ in the purified uniform state is $d^{-n/2}$ times this sum, so the two statements are equivalent
--   - encoding: an algorithm "that makes at most $t$ queries" → the intermediate state `alg.stateAt _ t` after $t\le T$ queries of a $T$-query algorithm; reason: an algorithm that has made $t'\le t$ queries has weight at most $t'\le t$; every such state is some `stateAt`
--   - encoding: initial state $|0\rangle_{QPW}$ followed by $U_0$ → the published `QueryAlg` with an arbitrary input-independent unit `start`; reason: the two give the same class of algorithms
--   - generalization: $\omega_d$ "some fixed d'th root of unity" (p.6) → any $\omega$ with $\omega^d=1$; reason: covers every fixed root the source may mean, including the primitive one
--   - encoding: domain $X=\mathbb Z_m$, inputs $x\in[m]^n$, phases $p\in\mathbb Z_m$ → `ZMod d`, inputs `Fin n → ZMod d`, query register `Fin n`; reason: Lean conventions; 0-based indices
-- source:
--   Beame–Holman–Kornerup, A Noise Operator Approach to Quantum Query Complexity and Time-Space Tradeoff Lower Bounds, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…), Corollary 2.9, p.10 (setting: §2.3, p.9, "We focus on the domain X = Zm and the input distribution being the uniform distribution on Xn")

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_QNoiseStab_phaseQuery
import Definitions.Def_QNoiseStab_fourierWeight
import Definitions.Def_QNoiseStab_fourierVec

namespace QNoiseStab

/-- **Corollary 2.9** (Beame–Holman–Kornerup, *A Noise Operator Approach to Quantum Query
Complexity and Time-Space Tradeoff Lower Bounds*, arXiv:2609.40334 (version of 2026-11-02, sha256
814fe20e…), p.10, in the setting of p.9: "We focus on the domain X = Zm and the input
distribution being the uniform distribution on Xn"). The state of any quantum query algorithm
that makes at most `t` queries to its input is a linear combination of states whose input register
in the Fourier basis `|ẑ⟩` has the property that `z` contains at most `t` non-0 entries.

Stated for every `T`-query algorithm `alg` with phase queries `phaseQuery ω x` (`ω ^ d = 1`) on
inputs `x ∈ Z_dⁿ`, every number of queries `t ≤ T` (the intermediate state `alg.stateAt _ t`),
every computational basis state `q` of the algorithm registers `QPW`, and every frequency `z` with
more than `t` nonzero entries: `Σ_x conj(⟨x|ẑ⟩) · ⟨q|ψ_t^x⟩ = 0`.

**Formalization Note** For the uniform input the joint state after `t` queries is
`Σ_x d^{-n/2} |ψ_t^x⟩|x⟩`; its input-register component at the basis state `q` is
`φ_q = Σ_x d^{-n/2} ψ_t^x(q) |x⟩`, and `⟨ẑ|φ_q⟩` is `d^{-n/2}` times the displayed sum. "A linear
combination of `|q⟩ ⊗ |ẑ⟩` with at most `t` nonzero `z_i`" is exactly the vanishing of this sum for
every `q` and every `z` of weight `> t`. The Fourier basis uses the primitive root `exp(2πi/d)`;
the oracle root `ω` is any `d`-th root of unity. -/
theorem corollary_2_9 {W : Type} [Fintype W] [DecidableEq W] {n d T : ℕ} [NeZero d] (ω : ℂ)
    (hω : ω ^ d = 1) (alg : QAlgorithms.QueryAlg (Fin n) (ZMod d) W T) (t : Fin (T + 1))
    (q : (Fin n × ZMod d) × W) (z : Fin n → ZMod d) (hz : t.val < fourierWeight z) :
    ∑ x : Fin n → ZMod d, star (fourierVec z x) * alg.stateAt (phaseQuery ω x) t q = 0 := by sorry

end QNoiseStab
