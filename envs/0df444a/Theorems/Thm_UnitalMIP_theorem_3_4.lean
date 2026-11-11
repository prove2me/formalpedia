-- Prove2me | Theorems.Thm_UnitalMIP_theorem_3_4
-- name    : UnitalMIP.theorem_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:40:49.467582+00:00
-- url     : https://prove2.me/theorems/3b181972-e57e-4e23-895b-41f1502ca7d7
-- title:
--   Theorem 3.4 — Pauli folding to $D\ge Ck^{64}\max\{t^2/\delta^{2/3},t/\delta^2\}$ qubits
-- statement:
--   There is an absolute constant $C>0$ with the following property. Fix a game $G$, let $n,k,D\ge1$, and use $n$ copies of a canonical state $\psi_{\boldsymbol\lambda}$. Let $0<\delta<1$, $t=\max\{|\mathcal A|,|\mathcal B|,2\}$, and let $(Q^x)_x$, $(R^y)_y$ be block approximants on $(\mathbb C^2)^{\otimes n}$ whose blocks have Pauli degree at most $k$ and satisfy $\|(Q^x)^\dagger Q^x-\mathbb 1\|_2,\ \|(R^y)^\dagger R^y-\mathbb 1\|_2\le\delta$ for every $x,y$. If $D\ge Ck^{64}\max\{t^2/\delta^{2/3},\,t/\delta^2\}$, there is one deterministic seed $\omega_0=(h,r)$ such that the folded blocks $\tilde Q^x_a=\Phi_{\omega_0}(Q^x_a)$, $\tilde R^y_b=\Phi_{\omega_0}(R^y_b)$ satisfy
--
--   $$
--   \mathbb E_{x\sim p_X}\|(\tilde Q^x)^\dagger\tilde Q^x-\mathbb 1\|_2^2,\ \ \mathbb E_{y\sim p_Y}\|(\tilde R^y)^\dagger\tilde R^y-\mathbb 1\|_2^2\le C\delta^{4/3},\qquad \mathrm{Val}_G(\tilde{\mathcal Q},\tilde{\mathcal R})\ge\mathrm{Val}_G(\mathcal Q,\mathcal R)-C\delta^{1/3}.
--   $$
--
--   This is the dimension reduction: the number of qubits becomes polynomial in $t$ and independent of $n$.
--
--   **Formalization Note** The canonical state has $\lambda_0=1$ and is a density matrix. $\mathrm{Val}_G(\tilde{\mathcal Q},\tilde{\mathcal R})$ is on $\psi_{\boldsymbol\lambda}^{\otimes D}$ and $\mathrm{Val}_G(\mathcal Q,\mathcal R)$ on $\psi_{\boldsymbol\lambda}^{\otimes n}$, both by (22). The seed is common to all blocks.
--
--   Differences from the source:
--   - encoding: Pauli degree at most $k$ ($\deg(0)=-\infty$) → every Pauli coefficient $\hat F(\alpha)$ with $|\alpha|>k$ vanishes; reason: the same condition, including the zero operator
--   - encoding: $\mathbb E_{x\sim p_X}$, $\mathbb E_{y\sim p_Y}$ → $\sum_x p_X(x)(\cdot)$, $\sum_y p_Y(y)(\cdot)$ with the marginals (15); reason: same expectations
--   - encoding: $\psi^{\otimes n}$ → `tensorPow ψ n`: the same operator with Alice's $n$ registers collected first; reason: a permutation of tensor factors; Alice holds the first qubit of every copy, as in the source
--   - encoding: $\mathrm{Tr}[(A^x_a\otimes(B^y_b)^T)\psi]$ in the value (16), (22) → the real part of this trace; reason: the trace is real for the positive semidefinite families and states to which the source applies the formula
--   - generalization: the §1.1 standing assumption (“Throughout, let ψ be a fixed two-qubit state … and assume that its entries are computable in polynomial time”, p.4) → every canonical state $\psi_\lambda$ with real $\lambda$, $\lambda_0=1$, no computability hypothesis on $\lambda$; reason: the statement is purely analytic; it specializes to the source's claim on every computable canonical state
-- source:
--   Dong, Jiang, Qin, Yao, Zhou, A Dichotomy for MIP* in the Presence of Unital Noise, arXiv:2609.39318 (version of 2026-11-03, sha256 56ebc59e…), Theorem 3.4, p.28

import Mathlib
import Definitions.Def_UnitalMIP_rhoMax
import Definitions.Def_UnitalMIP_omegaInf
import Definitions.Def_UnitalMIP_pauliString
import Definitions.Def_UnitalMIP_pauliFold
import Definitions.Def_UnitalMIP_canonicalState

open scoped Matrix

namespace UnitalMIP

/-- **Theorem 3.4** (Pauli folding; Dong, Jiang, Qin, Yao, Zhou, *A Dichotomy for MIP* in the Presence of Unital Noise*, arXiv:2609.39318 (version of 2026-11-03, sha256 56ebc59e…), p.28). There is an absolute constant `C > 0` such that: for
a game `G`, `n, k, D ≥ 1`, `n` copies of a canonical state `ψ_λ`, `0 < δ < 1`, `t = max{|𝒜|, |ℬ|, 2}`,
and block approximants `Q^x`, `R^y` on `(ℂ²)^{⊗n}` whose blocks have Pauli degree at most `k` and
which satisfy `‖(Q^x)†Q^x − 𝟙‖₂, ‖(R^y)†R^y − 𝟙‖₂ ≤ δ` for every `x`, `y`: if
`D ≥ C k⁶⁴ max{t²/δ^{2/3}, t/δ²}`, there is one deterministic seed `ω₀ = (h, r)` such that the folded
blocks `Q̃^x_a := Φ_{ω₀}(Q^x_a)`, `R̃^y_b := Φ_{ω₀}(R^y_b)` satisfy
`E_{x∼p_X} ‖(Q̃^x)†Q̃^x − 𝟙‖₂², E_{y∼p_Y} ‖(R̃^y)†R̃^y − 𝟙‖₂² ≤ C δ^{4/3}` and
`Val_G(𝒬̃, ℛ̃) ≥ Val_G(𝒬, ℛ) − C δ^{1/3}`.

**Formalization Note** The canonical state is `canonicalState λ` with `λ₀ = 1` and is required to be
a density matrix (a "state"); its marginals are then `𝟙/2`. `Val_G(𝒬̃, ℛ̃)` is on `ψ_λ^{⊗D}` and
`Val_G(𝒬, ℛ)` on `ψ_λ^{⊗n}`, both by formula (22). The expectations are `∑_x p_X(x)(·)` with the
marginals (15). The seed is a map `h : Fin n → Fin D` and signs `r ∈ (𝔽₂²)ⁿ`, common to all blocks. -/
theorem theorem_3_4 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (X Y A B : Type) [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
        (G : MIPRE.Game X Y A B) (n k D : ℕ), 1 ≤ n → 1 ≤ k → 1 ≤ D →
      ∀ (lam : Fin 2 × Fin 2 → ℝ), lam 0 = 1 → QAlgorithms.IsDensityMatrix (canonicalState lam) →
      ∀ (δ : ℝ), 0 < δ → δ < 1 →
      ∀ (Q : X → A → Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
        (R : Y → B → Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ),
        (∀ x a, HasPauliDegreeLE (Q x a) k) → (∀ y b, HasPauliDegreeLE (R y b) k) →
        (∀ x, nnorm2 (∑ a, (Q x a)ᴴ * Q x a - 1) ≤ δ) →
        (∀ y, nnorm2 (∑ b, (R y b)ᴴ * R y b - 1) ≤ δ) →
        C * (k : ℝ) ^ 64 *
            max ((max (max (Fintype.card A) (Fintype.card B)) 2 : ℝ) ^ 2 / δ ^ ((2 : ℝ) / 3))
              ((max (max (Fintype.card A) (Fintype.card B)) 2 : ℝ) / δ ^ 2) ≤ (D : ℝ) →
        ∃ (h : Fin n → Fin D) (r : Fin n → Fin 2 × Fin 2),
          (∑ x, pX G x * nnorm2 (∑ a, (pauliFold h r (Q x a))ᴴ * pauliFold h r (Q x a) - 1) ^ 2
            ≤ C * δ ^ ((4 : ℝ) / 3)) ∧
          (∑ y, pY G y * nnorm2 (∑ b, (pauliFold h r (R y b))ᴴ * pauliFold h r (R y b) - 1) ^ 2
            ≤ C * δ ^ ((4 : ℝ) / 3)) ∧
          val G (tensorPow (canonicalState lam) n) (fun x a => (Q x a)ᴴ * Q x a)
              (fun y b => (R y b)ᴴ * R y b) - C * δ ^ ((1 : ℝ) / 3) ≤
            val G (tensorPow (canonicalState lam) D)
              (fun x a => (pauliFold h r (Q x a))ᴴ * pauliFold h r (Q x a))
              (fun y b => (pauliFold h r (R y b))ᴴ * pauliFold h r (R y b)) := by sorry

end UnitalMIP
