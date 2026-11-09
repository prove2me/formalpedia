-- Prove2me | Theorems.Thm_QStateSearch_theorem_4
-- name    : QStateSearch.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:22:14.399587+00:00
-- url     : https://prove2.me/theorems/8398f3eb-39c5-4323-bdc1-9ecba074bf75
-- title:
--   Theorem 4 — $\mathbb E_\Psi\max_P|\mathrm{Acc}_{R_\Psi}-\mathrm{Acc}_I|\le2q\sqrt{(1+B\ln2)/D}$, the same for $\mathrm{val}$, and Theorem 1's fidelity form
-- statement:
--   Let $\mu_D$ be the Haar probability measure on pure states of $\mathbb C^D$ and let $V$ be a verifier that exchanges only classical messages with a prover, makes at most $q$ (controlled) queries to the distinguished $D$-dimensional oracle and receives at most $B$ padded prover bits. Then:
--
--   1. (Eq. (3))
--   $$
--   \mathbb E_{\Psi\leftarrow\mu_D}\Big[\max_P\big|\mathrm{Acc}_{R_\Psi}(V,P)-\mathrm{Acc}_I(V,P)\big|\Big]\le2q\sqrt{\frac{1+B\ln2}{D}},
--   $$
--   the maximum over deterministic classical provers (which may therefore depend on $\Psi$);
--   2. the same bound holds for $\mathbb E_{\Psi}\big[|\mathrm{val}_{R_\Psi}(V)-\mathrm{val}_I(V)|\big]$;
--   3. (Theorem 1) producing an output with constant average fidelity with $|\psi\rangle$ requires $(q+1)^2(B+1)=\Omega(D)$: for every $c>0$ there is $\kappa>0$ such that for every $D$, $q$, $B$ and every such verifier $V$,
--   $$
--   \mathbb E_{\Psi\leftarrow\mu_D}\Big[\max_P\langle\Psi|\rho^{V,P,\Psi}_{\mathrm{out}}|\Psi\rangle\Big]\ge c\quad\Longrightarrow\quad\kappa D\le(q+1)^2(B+1),
--   $$
--   where $\rho^{V,P,\psi}_{\mathrm{out}}$ is the verifier's output state with oracle $R_\psi$ and prover $P$, averaged over the protocol's randomness.
--
--   In each of 1 and 2 the integrand is also $\mu_D$-integrable. Classical interaction with an all-powerful prover who knows $\psi$ thus gives the verifier essentially no help in finding a Haar-random hidden state: constant advantage needs $q^2(B+1)=\Omega(D)$, as for a single classical witness.
--
--   **Formalization Note** $D$ is any natural number (the paper's $D=2^n$ is a special case of clause 3). The verifier's output register is its oracle-input register at the end of the run.
--
--   Differences from the source:
--   - generalization: a verifier whose classical messages alternate (p.9) and whose outgoing message registers are measured in the computational basis (p.8) → a `Verifier`: any finite list of unitary steps, controlled queries, verifier messages given by any instrument $\{K_a\}$ with $\sum_a K_a^\dagger K_a=I$, and padded prover messages received through unitaries, in any order; reason: the paper's verifiers are instances (alternation is a convention that padding makes harmless, p.9; measuring a register in the computational basis is $K_a=|a\rangle\langle a|\otimes I$)
--   - encoding: private quantum registers and private measurements; controlled and uncontrolled oracle calls → pure states on $\{0,1\}\times[D]\times W$ for a finite workspace $W$ with private measurements deferred; every call controlled; reason: the paper defers private measurements (p.10) and allows controlled calls (p.8); an uncontrolled call is a controlled one with the control set to $|1\rangle$
--   - encoding: Haar measure $\mu_D$ on pure states, equivalently on $\mathbb{CP}^{D-1}$ → `uniformSphere D`, the uniform probability measure on the unit sphere of $\mathbb C^D$; reason: every integrand depends on $\psi$ only through $|\psi\rangle\langle\psi|$, so the expectations agree
--   - encoding: $\max_P$; a fixed background oracle independent of $\Psi$ (p.12) → $\sup_P$ inside the integral; the background oracle is part of the verifier's unitary steps; reason: the supremum is attained; an oracle independent of $\Psi$ is a fixed unitary
--   - generalization: the bound on the two expectations of Theorem 4 → integrability of the integrand and the bound; reason: the integrand is bounded and measurable on the support of the measure; stating integrability excludes a Bochner integral that is $0$ by convention
--   - generalization: Theorem 1: a Haar-random $n$-qubit state, $D=2^n$ → any $D\in\mathbb N$; reason: $D=2^n$ is a special case
--   - reading: Theorem 1 (informal): constant average fidelity requires $(q+1)^2(B+1)=\Omega(2^n)$ → for every $c>0$ there is $\kappa>0$, uniform in $D,q,B,W,V$, with $c\le\mathbb E_\Psi[\sup_P F(V,P,\Psi)]\Rightarrow\kappa D\le(q+1)^2(B+1)$; reason: the strongest reading: the best $\Psi$-dependent prover inside the average and a constant depending only on the fidelity level
--   - reading: the verifier's output $\rho$ → the final reduced state of the oracle-input register, summed over transcripts (`fid`); reason: any output register can be swapped into the oracle-input register by a final unitary step
-- source:
--   Barhoush, Quantum State Search with Classical Interactive Advice, arXiv:2610.25657 (held version, sha256 2a16939a…3408), Theorem 4, Eq. (3), p.13; Theorem 1, p.2 (informal), fidelity defined on p.3

import Mathlib
import Definitions.Def_OptimalSpectrum_Entangled_uniformSphere
import Definitions.Def_QStateSearch_Verifier
import Definitions.Def_QStateSearch_numQueries
import Definitions.Def_QStateSearch_proverBits
import Definitions.Def_QStateSearch_AccW
import Definitions.Def_QStateSearch_val
import Definitions.Def_QStateSearch_refl
import Definitions.Def_QStateSearch_fid
open MeasureTheory OptimalSpectrum.Entangled

namespace QStateSearch

/-- **Theorem 4** (classical-interaction query bound), with **Theorem 1** as clause (c).
Let `V` exchange only classical messages, make at most `q` queries to the distinguished
`D`-dimensional oracle, and receive at most `B` padded prover bits. Then
(a) `E_Ψ[max_P |Acc_{R_Ψ}(V, P) − Acc_I(V, P)|] ≤ 2q√((1 + B ln 2)/D)` (Eq. (3)), the maximum over
deterministic classical provers;
(b) the same bound holds for `E_Ψ[|val_{R_Ψ}(V) − val_I(V)|]`;
(c) (Theorem 1) producing an output with constant average fidelity with `|ψ⟩` requires
`(q + 1)²(B + 1) = Ω(D)`: for every `c > 0` there is `κ > 0` such that average fidelity at least
`c` forces `κ D ≤ (q + 1)²(B + 1)`.

Barhoush, *Quantum State Search with Classical Interactive Advice*, arXiv:2610.25657
(held version, sha256 2a16939a…3408), Theorem 4, Eq. (3), p.13; Theorem 1, p.2 (informal), with "Fidelity means ⟨ψ|ρ|ψ⟩ for the
verifier's output ρ, averaged over the hidden state and the protocol's randomness", p.3.

**Formalization Note.** `Ψ ← μ_D` is `uniformSphere D` (uniform on the unit sphere of `ℂ^D`;
every integrand depends on `ψ` only through `|ψ⟩⟨ψ|`, so this is Haar measure on `CP^{D−1}`).
Verifiers are `Verifier D W` for any finite workspace `W`, with any order, number and alphabet of
messages; every query is controlled. `max_P` is `⨆ P` and sits inside the expectation, so the
prover may depend on `ψ`. `D` is any natural number (the paper's `D = 2ⁿ` is a special case).
Integrability is stated with each bound so that a junk Bochner integral cannot satisfy it. In (c)
the fidelity is `fid V P ψ` (output register = oracle-input register), the best `ψ`-dependent
prover is inside the average, and the constant `κ` depends only on `c`, uniformly in `D`, `q`, `B`,
`W` and `V`. -/
theorem theorem_4 :
    (∀ (D : ℕ) (W : Type) [Fintype W] [DecidableEq W] (V : Verifier D W) (q B : ℕ),
      numQueries V ≤ q → proverBits V ≤ B →
      Integrable (fun ψ => ⨆ P : Prover, |AccW V (refl ψ) P - AccW V 1 P|) (uniformSphere D) ∧
      ∫ ψ, (⨆ P : Prover, |AccW V (refl ψ) P - AccW V 1 P|) ∂(uniformSphere D)
        ≤ 2 * q * Real.sqrt ((1 + B * Real.log 2) / D)) ∧
    (∀ (D : ℕ) (W : Type) [Fintype W] [DecidableEq W] (V : Verifier D W) (q B : ℕ),
      numQueries V ≤ q → proverBits V ≤ B →
      Integrable (fun ψ => |val V (refl ψ) - val V 1|) (uniformSphere D) ∧
      ∫ ψ, |val V (refl ψ) - val V 1| ∂(uniformSphere D)
        ≤ 2 * q * Real.sqrt ((1 + B * Real.log 2) / D)) ∧
    (∀ c : ℝ, 0 < c → ∃ κ : ℝ, 0 < κ ∧
      ∀ (D : ℕ) (W : Type) [Fintype W] [DecidableEq W] (V : Verifier D W) (q B : ℕ),
        numQueries V ≤ q → proverBits V ≤ B →
        c ≤ ∫ ψ, (⨆ P : Prover, fid V P ψ) ∂(uniformSphere D) →
        κ * D ≤ ((q : ℝ) + 1) ^ 2 * ((B : ℝ) + 1)) := by sorry

end QStateSearch
