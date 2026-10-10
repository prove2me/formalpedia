-- Prove2me | Theorems.Thm_ScatPoly_Construction_lemma_3_4
-- name    : ScatPoly.Construction.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:17:17.125444+00:00
-- url     : https://prove2.me/theorems/734263a4-6481-40b1-9e9d-047d079f760f
-- title:
--   Lemma 3.4, p. 8 — {1, ρ}, {1, τ} are 𝔽_{q^t}-bases of 𝔽_{q^n} and the change of components (9)
-- statement:
--   Let $q = p^r$ be an odd prime power, $n = 2t$ with $t \ge 3$, $F = \mathbb F_{q^n}$, $\mathbb F_{q^t} \subseteq F$ the subfield of order $q^t$, $h \in F$ with $h^{q^t+1} = -1$, and $R, T$ as in (8). Let $\rho, \tau \in F^*$ with $\rho \in \ker R$ and $\tau \in \ker T$. Then:
--
--   1. $\{1, \rho\}$ and $\{1, \tau\}$ are $\mathbb F_{q^t}$-bases of $F$: every $\gamma \in F$ can be written in exactly one way as $\gamma = \lambda + \mu\rho$ with $\lambda, \mu \in \mathbb F_{q^t}$, and in exactly one way as $\gamma = \lambda' + \mu'\tau$ with $\lambda', \mu' \in \mathbb F_{q^t}$.
--   2. If $\tau = h^{q^{t-1}-q}\rho$ and $\gamma \in F$ has components $(\lambda_1, \mu_1)$ in the basis $\{1, \rho\}$, then its components in the basis $\{1, \tau\}$ are
--   $$\Bigl(\lambda_1 + \mu_1 \rho\bigl(1 - h^{q^{t-1}-q}\bigr),\ \mu_1\Bigr). \tag{9}$$
--
--   Together with (1), item 2 says: $\lambda_1 + \mu_1\rho(1 - h^{q^{t-1}-q})$ lies in $\mathbb F_{q^t}$ and $\gamma = \bigl(\lambda_1 + \mu_1\rho(1 - h^{q^{t-1}-q})\bigr) + \mu_1 \tau$, which by uniqueness identifies the components.
--
--   The lemma lets the main proof pass between coordinates adapted to $\ker R$ and to $\ker T$.
--
--   **Formalization Note.** "Basis" is stated by the unique-representation property rather than with Mathlib's `Basis` over a subfield type. The standing hypotheses $q$ odd and $h^{q^t+1} = -1$ of §3 are carried (the proof uses Proposition 3.2).
-- source:
--   Longobardi, Marino, Trombetti & Zhou, A large family of maximum scattered linear sets of PG(1, q^n) and their associated MRD codes, arXiv:2102.08287v3, p. 8, Lemma 3.4, display (9)

import Mathlib
import Definitions.Def_ScatCaps_LinearSets_Model
import Definitions.Def_ScatPoly_Construction_Model

namespace ScatPoly.Construction

open ScatCaps.LinearSets in
theorem lemma_3_4 (F : Type*) [Field F] [Fintype F] (p r t q : ℕ) [Fact p.Prime] [CharP F p]
    (hp : Odd p) (hr : 0 < r) (hq : q = p ^ r) (ht : 3 ≤ t)
    (hcard : Fintype.card F = q ^ (2 * t))
    (h : F) (hh : h ^ (q ^ t + 1) = -1)
    (ρ τ : F) (hρ0 : ρ ≠ 0) (hτ0 : τ ≠ 0) (hρ : Rmap q t h ρ = 0) (hτ : Tmap q t h τ = 0) :
    ((∀ γ : F, ∃! lm : F × F, lm.1 ∈ subfieldOf F p r t ∧ lm.2 ∈ subfieldOf F p r t ∧
        γ = lm.1 + lm.2 * ρ) ∧
      (∀ γ : F, ∃! lm : F × F, lm.1 ∈ subfieldOf F p r t ∧ lm.2 ∈ subfieldOf F p r t ∧
        γ = lm.1 + lm.2 * τ)) ∧
    (τ = h ^ q ^ (t - 1) / h ^ q * ρ →
      ∀ γ l₁ μ₁ : F, l₁ ∈ subfieldOf F p r t → μ₁ ∈ subfieldOf F p r t → γ = l₁ + μ₁ * ρ →
        l₁ + μ₁ * ρ * (1 - h ^ q ^ (t - 1) / h ^ q) ∈ subfieldOf F p r t ∧
        γ = (l₁ + μ₁ * ρ * (1 - h ^ q ^ (t - 1) / h ^ q)) + μ₁ * τ) := by sorry

end ScatPoly.Construction
