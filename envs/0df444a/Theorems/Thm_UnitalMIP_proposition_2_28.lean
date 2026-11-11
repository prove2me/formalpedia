-- Prove2me | Theorems.Thm_UnitalMIP_proposition_2_28
-- name    : UnitalMIP.proposition_2_28
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:40:54.848121+00:00
-- url     : https://prove2.me/theorems/29f5463e-927d-41f5-b4a7-16ff313a284f
-- title:
--   Proposition 2.28 — local-unitary canonical form $\psi_{\boldsymbol\lambda}=\frac14\sum_s\lambda_sP_s\otimes P_s^T$
-- statement:
--   Let $\psi\in M_2\otimes M_2$ be a state with $\psi_A=\psi_B=\mathbb 1/2$. There are single-qubit unitaries $U_A,U_B$ and real numbers $\boldsymbol\lambda=(\lambda_s)_{s\in\mathbb F_2^2}$ with $\lambda_0=1$ such that:
--
--   1. $\psi_{\boldsymbol\lambda}:=(U_A\otimes U_B)\psi(U_A\otimes U_B)^\dagger=\frac14\sum_{s}\lambda_sP_s\otimes P_s^T$;
--   2. for every $n\ge1$ and $\alpha,\beta\in(\mathbb F_2^2)^n$,
--   $$
--   \mathrm{Tr}\bigl[(P_\alpha\otimes P_\beta^T)\psi_{\boldsymbol\lambda}^{\otimes n}\bigr]=\mathbf 1\{\alpha=\beta\}\prod_{i=1}^n\lambda_{\alpha_i};
--   $$
--   3. the canonical correlation channel $\mathcal K=\mathcal K_{\psi_{\boldsymbol\lambda}}$ satisfies $\mathcal K(P_s)=\lambda_sP_s$, and $\rho_{\max}(\psi)=\max_{s\neq0}|\lambda_s|$;
--   4. for every game $G$, every $n\ge1$ and every POVM strategy $(\mathcal A,\mathcal B)$ on $\psi^{\otimes n}$, the operators $C^x_a=U_A^{\otimes n}A^x_a(U_A^{\otimes n})^\dagger$ and $D^y_b=\overline{U_B}^{\otimes n}B^y_b(\overline{U_B}^{\otimes n})^\dagger$ form a POVM strategy on $\psi_{\boldsymbol\lambda}^{\otimes n}$ with $\mathrm{Val}^{\psi_{\boldsymbol\lambda}^{\otimes n}}_G(\mathcal C,\mathcal D)=\mathrm{Val}^{\psi^{\otimes n}}_G(\mathcal A,\mathcal B)$.
--
--   Every later step works on the canonical form, where the correlation channel is diagonal in the Pauli basis.
--
--   **Formalization Note** "POVM strategy" in item 4 is: every $C^x_a$, $D^y_b$ positive semidefinite, $\sum_aC^x_a=\mathbb 1$, $\sum_bD^y_b=\mathbb 1$. The maximum over $s\ne0$ is written out over the three nonzero labels; $\overline{U}$ is entrywise conjugation.
--
--   Differences from the source:
--   - encoding: $\psi^{\otimes n}$ → `tensorPow ψ n`: the same operator with Alice's $n$ registers collected first; reason: a permutation of tensor factors; Alice holds the first qubit of every copy, as in the source
--   - encoding: $\mathrm{Tr}[(A^x_a\otimes(B^y_b)^T)\psi]$ in the value (16), (22) → the real part of this trace; reason: the trace is real for the positive semidefinite families and states to which the source applies the formula
--   - encoding: $\rho_{\max}$ as a maximum (Definition 2.20) → `sSup` of the set of admissible values $|\mathrm{Tr}[\psi(X\otimes Y^\dagger)]|$; reason: the set is nonempty and bounded and the maximum is attained by compactness, so the supremum equals it
--   - generalization: the §1.1 standing assumption (“Throughout, let ψ be a fixed two-qubit state … and assume that its entries are computable in polynomial time”, p.4) → any two-qubit density matrix ψ with the stated properties, with no computability hypothesis; reason: the statement is purely analytic and holds for every such state; it specializes to the source's claim on every computable ψ
-- source:
--   Dong, Jiang, Qin, Yao, Zhou, A Dichotomy for MIP* in the Presence of Unital Noise, arXiv:2609.39318 (version of 2026-11-03, sha256 56ebc59e…), Proposition 2.28, p.20

import Mathlib
import Definitions.Def_UnitalMIP_HasMaxMixedMarginals
import Definitions.Def_UnitalMIP_rhoMax
import Definitions.Def_UnitalMIP_omegaInf
import Definitions.Def_UnitalMIP_pauliString
import Definitions.Def_UnitalMIP_canonicalState

open scoped Matrix ComplexOrder

namespace UnitalMIP

/-- **Proposition 2.28** (Local-unitary canonical form; Dong, Jiang, Qin, Yao, Zhou, *A Dichotomy for MIP* in the Presence of Unital Noise*, arXiv:2609.39318 (version of 2026-11-03, sha256 56ebc59e…), p.20). Let `ψ ∈ M₂ ⊗ M₂` satisfy
`ψ_A = ψ_B = 𝟙/2`. There are single-qubit unitaries `U_A`, `U_B` and real numbers `λ = (λ_s)_{s ∈ 𝔽₂²}`
with `λ₀ = 1` such that
1. `ψ_λ := (U_A ⊗ U_B)ψ(U_A ⊗ U_B)† = ¼ ∑_s λ_s P_s ⊗ P_s^T`;
2. for every `n ≥ 1` and `α, β ∈ (𝔽₂²)ⁿ`, `Tr[(P_α ⊗ P_β^T) ψ_λ^{⊗n}] = 𝟏{α = β} ∏_i λ_{α_i}`;
3. `K_{ψ_λ}(P_s) = λ_s P_s` and `ρmax(ψ) = max_{s ≠ 0} |λ_s|`;
4. for every game, every `n ≥ 1` and every POVM strategy `(𝒜, ℬ)` on `ψ^{⊗n}`, the operators
   `C^x_a := U_A^{⊗n} A^x_a (U_A^{⊗n})†` and `D^y_b := \overline{U_B}^{⊗n} B^y_b (\overline{U_B}^{⊗n})†` form a POVM
   strategy on `ψ_λ^{⊗n}` with the same value.

**Formalization Note** `ψ` is a density matrix (a "state"). `ψ^{⊗n}` is the regrouped tensor
power `tensorPow` (Alice's `n` qubits first). The maximum over `s ≠ 0` is written out over the three
labels `(1,0)`, `(0,1)`, `(1,1)`. "POVM strategy" in item 4 is stated as: every `C^x_a` and `D^y_b`
is positive semidefinite and `∑_a C^x_a = 𝟙`, `∑_b D^y_b = 𝟙`. Entrywise conjugation is
`Matrix.map (starRingEnd ℂ)`. -/
theorem proposition_2_28 (ψ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hψ : QAlgorithms.IsDensityMatrix ψ) (hmm : HasMaxMixedMarginals ψ) :
    ∃ UA ∈ Matrix.unitaryGroup (Fin 2) ℂ, ∃ UB ∈ Matrix.unitaryGroup (Fin 2) ℂ,
    ∃ lam : Fin 2 × Fin 2 → ℝ, lam 0 = 1 ∧
      Matrix.kronecker UA UB * ψ * (Matrix.kronecker UA UB)ᴴ = canonicalState lam ∧
      (∀ n : ℕ, 1 ≤ n → ∀ α β : Fin n → Fin 2 × Fin 2,
        Matrix.trace (Matrix.kronecker (pauliString α) (pauliString β)ᵀ *
            tensorPow (canonicalState lam) n) =
          if α = β then ∏ i, ((lam (α i) : ℝ) : ℂ) else 0) ∧
      (∀ s : Fin 2 × Fin 2, corrChannel (canonicalState lam) (pauli s) = (lam s : ℂ) • pauli s) ∧
      rhoMax ψ = max (max |lam (1, 0)| |lam (0, 1)|) |lam (1, 1)| ∧
      (∀ (X Y A B : Type) [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
        (G : MIPRE.Game X Y A B) (n : ℕ), 1 ≤ n →
        ∀ (SA : X → MIPRE.POVM A (Fin n → Fin 2)) (SB : Y → MIPRE.POVM B (Fin n → Fin 2)),
          let C : X → A → Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ := fun x a =>
            kronPow UA * povmMats SA x a * (kronPow UA)ᴴ
          let D : Y → B → Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ := fun y b =>
            kronPow (UB.map (starRingEnd ℂ)) * povmMats SB y b *
              (kronPow (UB.map (starRingEnd ℂ)))ᴴ
          (∀ x, (∀ a, (C x a).PosSemidef) ∧ ∑ a, C x a = 1) ∧
          (∀ y, (∀ b, (D y b).PosSemidef) ∧ ∑ b, D y b = 1) ∧
          val G (tensorPow (canonicalState lam) n) C D =
            val G (tensorPow ψ n) (povmMats SA) (povmMats SB)) := by sorry

end UnitalMIP
