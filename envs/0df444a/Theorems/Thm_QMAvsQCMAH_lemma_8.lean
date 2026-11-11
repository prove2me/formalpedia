-- Prove2me | Theorems.Thm_QMAvsQCMAH_lemma_8
-- name    : QMAvsQCMAH.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:20:39.094418+00:00
-- url     : https://prove2.me/theorems/47166584-5834-48b9-8132-89113dda95a9
-- title:
--   Lemma 8 — joint inclusion bounds give contractive simultaneous incompressibility, also after adding noise
-- statement:
--   Let $F_\lambda\subseteq\mathcal X_\lambda$ be random, $\mathcal X_\lambda$ finite. Suppose $\rho(\lambda)>0$ tends to zero and, for all sufficiently large $\lambda$ and every $1\le r\le2^\lambda$,
--   $$\Pr_{F_\lambda}[u_1,\dots,u_r\in F_\lambda]\le\rho(\lambda)^r\quad\text{for all distinct }u_1,\dots,u_r\in\mathcal X_\lambda.$$
--   Then $(F_\lambda)_\lambda$ satisfies $\gamma$-contractive simultaneous incompressibility for $\gamma(\lambda)=\log_2(1/\rho(\lambda))$. If $B_\lambda\leftarrow\mathrm{Bernoulli}(\beta(\lambda))^{\mathcal X_\lambda}$ is sampled independently of $F_\lambda$ and $\rho(\lambda)+\beta(\lambda)\to0$, the same holds for $F_\lambda\cup\mathrm{supp}(B_\lambda)$ with $\rho+\beta$ in place of $\rho$.
--
--   It supplies the incompressibility hypothesis of Theorem 5 for codeword-hash pairs and sparse noise.
--
--   Differences from the source:
--   - reading: Bernoulli(β(λ)) → β(λ) ∈ [0, 1] as a hypothesis; reason: a Bernoulli parameter is a probability
--   - encoding: the random set F_λ ∪ supp(B_λ) → its law unionW (F λ) (β λ); reason: paper.md decision 13
-- source:
--   Cakan, Classical Oracle Separation of QMA from the QCMA Hierarchy and Quantum Cryptography Even When P = QCMA, STOC 2027 submission (held version, sha256 336ce016…c897), Lemma 8, p.29 (PDF p.32), Equation (21)

import Definitions.Def_QMAvsQCMAH_IsCSI
import Definitions.Def_QMAvsQCMAH_unionW

set_option autoImplicit false

namespace QMAvsQCMAH

/-- **Lemma 8 (Contractive simultaneous incompressibility and independent noise).** Let
`F_λ ⊆ X_λ` be random, `X_λ` finite. Suppose `ρ(λ) > 0` tends to zero and, for all sufficiently
large `λ` and every `1 ≤ r ≤ 2^λ`, `Pr[u_1, …, u_r ∈ F_λ] ≤ ρ(λ)^r` for all distinct `u_1, …, u_r`.
Then `(F_λ)` satisfies γ-contractive simultaneous incompressibility for `γ(λ) = log₂(1/ρ(λ))`.
If `B_λ ← Bernoulli(β(λ))^{X_λ}` is sampled independently of `F_λ` and `ρ + β → 0`, the same holds
for `F_λ ∪ supp(B_λ)` with `ρ + β` in place of `ρ`.

Cakan, *Classical Oracle Separation of QMA from the QCMA Hierarchy and Quantum Cryptography
Even When P = QCMA*, STOC 2027 submission (held version, sha256 336ce016…c897), Lemma 8, p.29 (PDF p.32), Equation (21).

**Formalization Note.** Both parts are clauses. `β(λ) ∈ [0, 1]` (a Bernoulli parameter). The
law of `F_λ ∪ supp(B_λ)` is `unionW`. A set of `r` distinct inputs is a `Finset` of card `r`. -/
theorem lemma_8 (X : ℕ → Type) [∀ n, Fintype (X n)] [∀ n, DecidableEq (X n)] (F : ∀ n, Finset (X n) → ℝ) (hF : ∀ n, IsDist (F n)) (ρ : ℕ → ℝ) (hρ : ∀ n, 0 < ρ n) (hρ0 : Filter.Tendsto ρ Filter.atTop (nhds 0)) (hinc : ∃ n0 : ℕ, ∀ n ≥ n0, ∀ S : Finset (X n), 1 ≤ S.card → S.card ≤ 2 ^ n → prob (F n) (fun T => S ⊆ T) ≤ ρ n ^ S.card) : IsCSI X F (fun n => Real.logb 2 (1 / ρ n)) ∧ ∀ β : ℕ → ℝ, (∀ n, 0 ≤ β n ∧ β n ≤ 1) → Filter.Tendsto (fun n => ρ n + β n) Filter.atTop (nhds 0) → IsCSI X (fun n => unionW (F n) (β n)) (fun n => Real.logb 2 (1 / (ρ n + β n))) := by sorry

end QMAvsQCMAH
