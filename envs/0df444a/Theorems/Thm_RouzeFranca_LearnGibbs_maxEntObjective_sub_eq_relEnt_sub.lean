-- Prove2me | Theorems.Thm_RouzeFranca_LearnGibbs_maxEntObjective_sub_eq_relEnt_sub
-- name    : RouzeFranca.LearnGibbs.maxEntObjective_sub_eq_relEnt_sub
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:47:53.967549+00:00
-- url     : https://prove2.me/theorems/40cf5bd4-5448-411c-a443-0744cf6c87d8
-- title:
--   Lemma A.1 — $f(\mu)-f(\xi)=D(\sigma(\lambda)\|\sigma(\mu))-D(\sigma(\lambda)\|\sigma(\xi))$
-- statement:
--   Let $E_1,\dots,E_m$ be Hermitian observables on $n$ qubits, $\beta>0$, and $\lambda,\mu,\xi\in\mathbb R^m$. With $f(\mu)=\log\mathcal Z(\mu)+\beta\sum_ie_i(\lambda)\mu_i$,
--   $$
--   f(\mu)-f(\xi)=D\bigl(\sigma(\lambda)\|\sigma(\mu)\bigr)-D\bigl(\sigma(\lambda)\|\sigma(\xi)\bigr).
--   $$
--
--   Both relative entropies are finite because Gibbs states have full rank. The lemma ties the decrease of the objective during the maximum-entropy optimization to the decrease of the relative entropy between the target state and the current iterate.
--
--   **Formalization Note** The identity is stated in the extended reals; both sides are real numbers. Natural logarithm.
--
--   Differences from the source:
--   - generalization: µ, ξ ∈ ℝ^m with ∥µ∥_ℓ∞, ∥ξ∥_ℓ∞ ≤ 1; σ(λ) a Gibbs state in the sense of Definition A.1 (∥λ∥_ℓ∞ ≤ 1, E_i linearly independent, ∥E_i∥_∞ ≤ 1) → any λ, μ, ξ ∈ ℝ^m, any Hermitian E_i; reason: the identity holds for all real parameters; the source's case is a special case
--   - encoding: D(·∥·), real identity → relEnt in EReal (⊤ off support), identity in EReal; reason: Lean convention; both relative entropies are finite here, so the same instances
-- source:
--   Rouzé, Stilck França, Learning quantum many-body systems from a few copies, arXiv:2107.03333v4, Lemma A.1, Eq. (24), pp. 15–16

import Mathlib
import Definitions.Def_RouzeFranca_LearnGibbs_gibbs
import Definitions.Def_RouzeFranca_LearnGibbs_maxEntObjective
import Definitions.Def_RouzeFranca_LearnGibbs_relEnt

namespace RouzeFranca.LearnGibbs

/-- **Lemma A.1 (objective differences are relative-entropy differences).** For Hermitian
observables `E₁, …, E_m`, `β > 0` and parameters `λ, μ, ξ ∈ ℝ^m`, with
`f(μ) = log Z(μ) + β ∑ᵢ eᵢ(λ) μᵢ`,
`f(μ) − f(ξ) = D(σ(λ)‖σ(μ)) − D(σ(λ)‖σ(ξ))`.

Rouzé, Stilck França, arXiv:2107.03333v4, Lemma A.1, Eq. (24), pp. 15–16: "Let σ(λ) ∈ D_{d^n} be
a Gibbs state with respect to a set of observables E at inverse temperature β > 0 and define, for
any µ ∈ R^m, f(µ) := log(Z(µ)) + β Σ_{i=1}^m e_i(λ) µ_i. (24) Then for any other two vectors
µ, ξ ∈ R^m with ∥µ∥_ℓ∞, ∥ξ∥_ℓ∞ ≤ 1: f(µ) − f(ξ) = D(σ(λ)∥σ(µ)) − D(σ(λ)∥σ(ξ))."

**Formalization Note.** `lam` is the paper's `λ`. The identity is stated in `EReal`; both relative
entropies are finite because Gibbs states have full rank, so the `EReal` subtraction is ordinary
real subtraction (no `⊤ − ⊤`). Stated for all real `λ, μ, ξ` (the paper restricts `μ, ξ` and,
through Definition A.1, `λ` to the ℓ∞ unit ball, and assumes the `Eᵢ` linearly independent with
`‖Eᵢ‖∞ ≤ 1`; none is needed). Natural logarithm. -/
theorem maxEntObjective_sub_eq_relEnt_sub {n m : ℕ} (E : Fin m → Mat n)
    (hE : ∀ i, (E i).IsHermitian) (β : ℝ) (hβ : 0 < β) (lam μ ξ : EuclideanSpace ℝ (Fin m)) :
    ((maxEntObjective E β lam μ - maxEntObjective E β lam ξ : ℝ) : EReal) =
      relEnt (gibbs E β lam) (gibbs E β μ) - relEnt (gibbs E β lam) (gibbs E β ξ) := by sorry

end RouzeFranca.LearnGibbs
