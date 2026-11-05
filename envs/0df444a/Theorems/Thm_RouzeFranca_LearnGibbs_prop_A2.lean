-- Prove2me | Theorems.Thm_RouzeFranca_LearnGibbs_prop_A2
-- name    : RouzeFranca.LearnGibbs.prop_A2
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:47:35.175491+00:00
-- url     : https://prove2.me/theorems/6c1a7d06-c41c-41db-92ed-424e6b8b5388
-- title:
--   Proposition A.2 — $\|\sigma(\mu)-\sigma(\lambda)\|_{tr}^2\le D(\sigma(\mu)\|\sigma(\lambda))+D(\sigma(\lambda)\|\sigma(\mu))=-\beta\langle\lambda-\mu|e(\lambda)-e(\mu)\rangle$
-- statement:
--   Let $E_1,\dots,E_m$ be Hermitian observables on $n$ qubits, $\beta>0$ and $\lambda,\mu\in\mathbb R^m$. Then
--   $$
--   \|\sigma(\mu)-\sigma(\lambda)\|_{tr}^2\ \le\ D\bigl(\sigma(\mu)\|\sigma(\lambda)\bigr)+D\bigl(\sigma(\lambda)\|\sigma(\mu)\bigr)\ =\ -\beta\,\bigl\langle\lambda-\mu\,\big|\,e(\lambda)-e(\mu)\bigr\rangle ,
--   $$
--   where $\|X\|_{tr}=\operatorname{tr}|X|$ is the trace norm (without a factor $\tfrac12$) and $\langle\cdot|\cdot\rangle$ is the Euclidean inner product on $\mathbb R^m$. Both the inequality and the identity are asserted.
--
--   The identity makes the symmetrized relative entropy between two Gibbs states computable from their parameters and expectation values alone; the inequality turns it into a trace-distance bound.
--
--   **Formalization Note** Stated in the extended reals; all relative entropies here are finite. Natural logarithm.
--
--   Differences from the source:
--   - generalization: σ(µ), σ(λ) Gibbs states in the sense of Definition A.1 (∥λ∥_ℓ∞, ∥µ∥_ℓ∞ ≤ 1, E_i linearly independent, ∥E_i∥_∞ ≤ 1) → any λ, μ ∈ ℝ^m, any Hermitian E_i; reason: both clauses hold for all real parameters; the source's case is a special case
--   - encoding: D(·∥·), ∥·∥_tr = tr|·| → relEnt in EReal (⊤ off support), WildeQIT.traceNorm (no ½), statement in EReal; reason: Lean convention; same instances
-- source:
--   Rouzé, Stilck França, Learning quantum many-body systems from a few copies, arXiv:2107.03333v4, Proposition A.2, Eq. (22), p. 15

import Mathlib
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_RouzeFranca_LearnGibbs_gibbs
import Definitions.Def_RouzeFranca_LearnGibbs_relEnt

namespace RouzeFranca.LearnGibbs

/-- **Proposition A.2 (symmetric relative entropy of Gibbs states).** For Hermitian observables
`E₁, …, E_m`, `β > 0` and parameters `λ, μ ∈ ℝ^m`,
`‖σ(μ) − σ(λ)‖²_tr ≤ D(σ(μ)‖σ(λ)) + D(σ(λ)‖σ(μ)) = −β ⟨λ − μ | e(λ) − e(μ)⟩`.

Rouzé, Stilck França, arXiv:2107.03333v4, Proposition A.2, Eq. (22), p. 15: "Let σ(µ), σ(λ) ∈
D_{d^n} be Gibbs states with respect to a set of observables E at inverse temperature β. Denote
e(λ) = (tr[σ(λ)E_i])_i ∈ R^m. Then ∥σ(µ) − σ(λ)∥²_tr ≤ D(σ(µ)∥σ(λ)) + D(σ(λ)∥σ(µ)) =
−β⟨λ − µ|e(λ) − e(µ)⟩."

**Formalization Note.** `lam` is the paper's `λ`. Both clauses (the inequality and the identity)
are stated, in `EReal`. `‖X‖_tr = tr|X|` is `WildeQIT.traceNorm`, **without** a factor `½`
(p. 14). Natural logarithm. `β > 0` from Definition A.1; `λ, μ` are any real vectors and the
`Eᵢ` need not be linearly independent or of norm at most one. -/
theorem prop_A2 {n m : ℕ} (E : Fin m → Mat n) (hE : ∀ i, (E i).IsHermitian) (β : ℝ)
    (hβ : 0 < β) (lam μ : EuclideanSpace ℝ (Fin m)) :
    (((WildeQIT.traceNorm (gibbs E β μ - gibbs E β lam)) ^ 2 : ℝ) : EReal) ≤
        relEnt (gibbs E β μ) (gibbs E β lam) + relEnt (gibbs E β lam) (gibbs E β μ) ∧
      relEnt (gibbs E β μ) (gibbs E β lam) + relEnt (gibbs E β lam) (gibbs E β μ) =
        ((-β * inner ℝ (lam - μ) (expect E β lam - expect E β μ) : ℝ) : EReal) := by sorry

end RouzeFranca.LearnGibbs
