-- Prove2me | Theorems.Thm_QubitTracking_lemma_7_6
-- name    : QubitTracking.lemma_7_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:29:43.601483+00:00
-- url     : https://prove2.me/theorems/fb08a46e-628a-4b51-acd5-ecabe0f7c650
-- title:
--   Lemma 7.6 ([VZ21] Lemma 5.4) — EPR-pair rigidity: the displayed $\Phi_{\mathbf B}$ is an isometry with EPR fidelity $1-O(\varepsilon^{1/2})$
-- statement:
--   Let $|\psi\rangle_{\mathbf A\mathbf B}\in(\mathbb C^2)^{\otimes n}_{\mathbf A}\otimes\mathcal H_{\mathbf B}$ be a unit vector, and suppose that for every $a\in\{0,1\}^n$ there are observables $X_{\mathbf B}(a)$, $Z_{\mathbf B}(a)$ on $\mathcal H_{\mathbf B}$ with
--   $$\mathbb E_a\big\|(\sigma^{\mathbf A}_W(a)-W_{\mathbf B}(a))|\psi\rangle\big\|^2\le\varepsilon\qquad(W\in\{X,Z\})$$
--   for some $0\le\varepsilon\le1$ ($a$ uniform). Then the map $\Phi_{\mathbf B}|\varphi\rangle=\big(2^{-n}\sum_{a,b}X_{\mathbf B}(a)Z_{\mathbf B}(b)\otimes\sigma_X(a)\sigma_Z(b)\otimes I\big)|\varphi\rangle|\mathrm{EPR}\rangle^{\otimes n}$ is an isometry $\mathcal H_{\mathbf B}\to(\mathbb C^2)^{\otimes n}_{\mathbf B'}\otimes\hat{\mathcal H}_{\mathbf B}$ and
--   $$\mathrm{Tr}\big(\langle\mathrm{EPR}|^{\otimes n}_{\mathbf A\mathbf B'}((I_{\mathbf A}\otimes\Phi_{\mathbf B})(|\psi\rangle\langle\psi|))|\mathrm{EPR}\rangle^{\otimes n}_{\mathbf A\mathbf B'}\big)=1-O(\varepsilon^{1/2}).$$
--
--   It converts approximate Pauli observables on the prover's side into an explicit extraction of $n$ EPR pairs.
--
--   Differences from the source:
--   - reading: observables X_𝐁(a), Z_𝐁(a) → self-adjoint operators with square 1; reason: binary (±1-valued) observables, as in [VZ21]; they make the displayed Φ_𝐁 an isometry
--   - encoding: ℋ_𝐁 arbitrary → ℋ_𝐁 = ℂ^β for any finite type β; |ψ⟩ a unit vector; reason: the paper's states are finite dimensional
--   - encoding: = 1 − O(ε^{1/2}) → ≥ 1 − C ε^{1/2} for a universal constant C > 0 chosen before all data; reason: the fidelity is at most 1, so the O-statement is this lower bound
--   - reading: there exists an isometry … Moreover, … Precisely, Φ_𝐁 is defined by (display) → the displayed Φ_𝐁 (rigidityIso) is an isometry and attains the bound; reason: the 'Precisely' sentence fixes the isometry; the circuit-size sentence describes how it is implemented
-- source:
--   Bartusek, Huang, Orshansky, Yuen, How To Track Qubits Through Space and Time (Or: Sailing in a Quantum Boat), arXiv:2605.30732 (held version, sha256 bf98e5b5…), Lemma 7.6, pp.53–54

import Definitions.Def_QubitTracking_rigidityIso

set_option autoImplicit false

open Matrix

namespace QubitTracking

/-- **Lemma 7.6** (EPR Pair Rigidity, [VZ21] Lemma 5.4; Bartusek, Huang, Orshansky, Yuen, *How To
Track Qubits Through Space and Time*, arXiv:2605.30732 (held version, sha256 bf98e5b5…),
Lemma 7.6, pp.53–54). Let `|ψ⟩_{𝐀𝐁} ∈ (ℂ²)^{⊗n}_𝐀 ⊗ ℋ_𝐁` be a unit vector. Suppose that for every
`a ∈ {0,1}^n` there are observables `X_𝐁(a)`, `Z_𝐁(a)` on `ℋ_𝐁` such that for `W ∈ {X, Z}`
`𝔼_a ‖(σ^𝐀_W(a) − W_𝐁(a))|ψ⟩‖² ≤ ε` for some `0 ≤ ε ≤ 1` (`a` uniform). Then the operator
`Φ_𝐁|φ⟩ = (2^{-n} ∑_{a,b} X_𝐁(a)Z_𝐁(b) ⊗ σ_X(a)σ_Z(b) ⊗ I)|φ⟩_𝐁|EPR⟩^{⊗n}`, from `ℋ_𝐁` to
`((ℂ²)^{⊗n})_{𝐁′} ⊗ ℋ̂_𝐁` (`ℋ̂_𝐁 = ℋ_𝐁 ⊗ (ℂ²)^{⊗n}`, `𝐁′` the last `n` copies of `ℂ²`), is an
isometry and
`Tr(⟨EPR|^{⊗n}_{𝐀𝐁′} ((I_𝐀 ⊗ Φ_𝐁)(|ψ⟩⟨ψ|)) |EPR⟩^{⊗n}_{𝐀𝐁′}) = 1 − O(ε^{1/2})`.

**Formalization Note** `ℋ_𝐁 = ℂ^β` is finite dimensional; an observable is self-adjoint with
square `1`; `= 1 − O(ε^{1/2})` is the lower bound `≥ 1 − C ε^{1/2}` for a universal constant `C`
(the fidelity is at most `1` automatically). The "Moreover" clause is the displayed formula, which
is the isometry `rigidityIso`. -/
theorem lemma_7_6 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (β : Type) [Fintype β] [DecidableEq β] (ψ : Bits (Fin n) × β → ℂ),
        normSq ψ = 1 →
        ∀ (X Z : Bits (Fin n) → Matrix β β ℂ), (∀ a, IsObservable (X a)) → (∀ a, IsObservable (Z a)) →
        ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
          avg (fun a : Bits (Fin n) =>
            normSq (fun p => actLeft (sigmaX a) ψ p - actRight (X a) ψ p)) ≤ ε →
          avg (fun a : Bits (Fin n) =>
            normSq (fun p => actLeft (sigmaZ a) ψ p - actRight (Z a) ψ p)) ≤ ε →
          IsIsometry (rigidityIso X Z) ∧
            1 - C * Real.sqrt ε ≤ eprOverlap (actRight (rigidityIso X Z) ψ) := by sorry

end QubitTracking
