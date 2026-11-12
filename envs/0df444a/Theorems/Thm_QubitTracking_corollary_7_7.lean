-- Prove2me | Theorems.Thm_QubitTracking_corollary_7_7
-- name    : QubitTracking.corollary_7_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:29:43.519601+00:00
-- url     : https://prove2.me/theorems/e23002a8-f019-4b80-adad-1ca023722736
-- title:
--   Corollary 7.7 — EPR-pair rigidity from two incompatible extractors
-- statement:
--   Let $|\psi\rangle_{\mathbf A\mathbf B}\in(\mathbb C^2)^{\otimes n}_{\mathbf A}\otimes\mathcal H_{\mathbf B}$ be a unit vector, $\tilde{\mathbf B}$ the first $n$ qubits of the target register and $\Pi_{\mathrm{eq}}=\sum_x|x\rangle\langle x|_{\mathbf A}\otimes|x\rangle\langle x|_{\tilde{\mathbf B}}\otimes I_{\tilde{\mathbf B}'}$. Suppose there are isometries $\mathcal U^{\mathbf B}_X,\mathcal U^{\mathbf B}_Z:\mathcal H_{\mathbf B}\to\mathcal H_{\tilde{\mathbf B}}\otimes\mathcal H_{\tilde{\mathbf B}'}$ with
--   $$\|\Pi_{\mathrm{eq}}(I_{\mathbf A}\otimes\mathcal U^{\mathbf B}_Z)|\psi\rangle\|^2\ge1-\varepsilon,\qquad\|\Pi_{\mathrm{eq}}(H^{\otimes n}_{\mathbf A}\otimes\mathcal U^{\mathbf B}_X)|\psi\rangle\|^2\ge1-\varepsilon.$$
--   Then:
--
--   1. there is an isometry $\Phi_{\mathbf B}:\mathcal H_{\mathbf B}\to(\mathbb C^2)^{\otimes n}_{\mathbf B'}\otimes\hat{\mathcal H}_{\mathbf B}$ with EPR fidelity $1-O(\varepsilon^{1/2})$ on $\mathbf A\mathbf B'$;
--   2. such a $\Phi_{\mathbf B}$ is built from controlled uses of $\mathcal U_X$, $\mathcal U_Z$: for any unitaries $V_X,V_Z$ implementing them on an ancilla state $|\alpha_0\rangle$, the observables $W_{\mathbf B}(a)=V_W^\dagger(\sigma^{\tilde{\mathbf B}}_Z(a)\otimes I)V_W$ give, through the formula of Lemma 7.6, the isometry $|\varphi\rangle\mapsto\Phi(|\varphi\rangle|\alpha_0\rangle)$ with that fidelity.
--
--   It is how Theorem 7.9 combines the extractors of Lemma 7.1 and Corollary 7.5.
--
--   Differences from the source:
--   - encoding: ℋ_𝐁, ℋ_{𝐁̃′} arbitrary → finite types β, γ (and a finite ancilla type α); |ψ⟩ a unit vector; reason: the paper's states are finite dimensional
--   - encoding: = 1 − O(ε^{1/2}) → ≥ 1 − C ε^{1/2} for a universal constant C > 0 chosen before all data; reason: the fidelity is at most 1
--   - reading: Moreover, Φ_𝐁 can be implemented as an O(n)-size circuit using controlled 𝒰_X, 𝒰_Z as black boxes → for every unitary dilation V_W of 𝒰_W, the isometry built by Lemma 7.6's formula from W_𝐁(a) = V_W†(σ_Z(a) ⊗ I)V_W, applied to |φ⟩|α₀⟩, attains the bound; reason: the proof (p.54) builds the observables this way, reading 𝒰† as 'the reverse procedure of 𝒰', i.e. the inverse of a unitary implementation
-- source:
--   Bartusek, Huang, Orshansky, Yuen, How To Track Qubits Through Space and Time (Or: Sailing in a Quantum Boat), arXiv:2605.30732 (held version, sha256 bf98e5b5…), Corollary 7.7, p.54

import Definitions.Def_QubitTracking_rigidityIso

set_option autoImplicit false

open Matrix

namespace QubitTracking

/-- **Corollary 7.7** (EPR Pair Rigidity (corollary); Bartusek, Huang, Orshansky, Yuen, *How To Track
Qubits Through Space and Time*, arXiv:2605.30732 (held version, sha256 bf98e5b5…), Corollary 7.7,
p.54). Let `|ψ⟩_{𝐀𝐁} ∈ (ℂ²)^{⊗n}_𝐀 ⊗ ℋ_𝐁` be a unit vector, `𝐁̃` the first `n` qubits of the
target register, `Π_eq = ∑_x |x⟩⟨x|_𝐀 ⊗ |x⟩⟨x|_{𝐁̃} ⊗ I_{𝐁̃′}`. Suppose there are two isometries
`𝒰^𝐁_X, 𝒰^𝐁_Z : ℋ_𝐁 → ℋ_{𝐁̃} ⊗ ℋ_{𝐁̃′}` with `‖Π_eq(I_𝐀 ⊗ 𝒰^𝐁_Z)|ψ⟩‖² ≥ 1 − ε` and
`‖Π_eq(H^{⊗n}_𝐀 ⊗ 𝒰^𝐁_X)|ψ⟩‖² ≥ 1 − ε`. Then
1. there is an isometry `Φ_𝐁 : ℋ_𝐁 → ((ℂ²)^{⊗n})_{𝐁′} ⊗ ℋ̂_𝐁` with
   `Tr(⟨EPR|^{⊗n}_{𝐀𝐁′} ((I_𝐀 ⊗ Φ_𝐁)(|ψ⟩⟨ψ|)) |EPR⟩^{⊗n}_{𝐀𝐁′}) = 1 − O(ε^{1/2})`;
2. (*Moreover*) such a `Φ_𝐁` is obtained from controlled uses of `𝒰^𝐁_X`, `𝒰^𝐁_Z` as black boxes:
   for any unitaries `V_X, V_Z` on `ℋ_𝐁 ⊗ (ancilla)` implementing `𝒰_X, 𝒰_Z` on the ancilla state
   `|α₀⟩`, the observables `W_𝐁(a) = V_W†(σ^{𝐁̃}_Z(a) ⊗ I_{𝐁̃′})V_W` (`W ∈ {X, Z}`, as in the proof,
   p.54) give, through Lemma 7.6's formula, the isometry `|φ⟩ ↦ Φ(|φ⟩|α₀⟩)` with that fidelity.

**Formalization Note** `ℋ_𝐁 = ℂ^β`, `ℋ_{𝐁̃′} = ℂ^γ`, the ancilla `ℂ^α` are finite dimensional;
`1 − O(ε^{1/2})` is `≥ 1 − C ε^{1/2}` for a universal `C`. The proof's "`𝒰†` means the reverse
procedure of `𝒰`" is the inverse `V_W†` of a unitary implementation; the circuit-size sentence is
pinned to this construction. -/
theorem corollary_7_7 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (β γ : Type) [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
        (ψ : Bits (Fin n) × β → ℂ), normSq ψ = 1 →
        ∀ (UX UZ : Matrix (Bits (Fin n) × γ) β ℂ), IsIsometry UX → IsIsometry UZ →
        ∀ ε : ℝ,
          1 - ε ≤ eqOverlap (actRight UZ ψ) →
          1 - ε ≤ eqOverlap (actLeft (hadamard (Fin n)) (actRight UX ψ)) →
          (∃ (H' : Type) (_ : Fintype H') (_ : DecidableEq H')
              (Φ : Matrix (H' × Bits (Fin n)) β ℂ),
            IsIsometry Φ ∧ 1 - C * Real.sqrt ε ≤ eprOverlap (actRight Φ ψ)) ∧
          ∀ (α : Type) [Fintype α] [DecidableEq α] (α₀ : α)
            (VX VZ : Matrix (Bits (Fin n) × γ) (β × α) ℂ),
            VXᴴ * VX = 1 → VX * VXᴴ = 1 → VZᴴ * VZ = 1 → VZ * VZᴴ = 1 →
            (∀ g h, VX g (h, α₀) = UX g h) → (∀ g h, VZ g (h, α₀) = UZ g h) →
            let Wop : Matrix (Bits (Fin n) × γ) (β × α) ℂ → Bits (Fin n) → Matrix (β × α) (β × α) ℂ :=
              fun V a => Vᴴ * kroneckerMap (· * ·) (sigmaZ a) (1 : Matrix γ γ ℂ) * V
            let Φ : Matrix (((β × α) × Bits (Fin n)) × Bits (Fin n)) β ℂ :=
              rigidityIso (Wop VX) (Wop VZ) *
                (Matrix.of fun (p : β × α) (h : β) => if p.1 = h ∧ p.2 = α₀ then (1 : ℂ) else 0)
            IsIsometry Φ ∧ 1 - C * Real.sqrt ε ≤ eprOverlap (actRight Φ ψ) := by sorry

end QubitTracking
