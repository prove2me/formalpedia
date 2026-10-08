-- Prove2me | Theorems.Thm_VeinottSensitiveDP_Sensitive_lemma_5
-- name    : VeinottSensitiveDP.Sensitive.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:52:41.035144+00:00
-- url     : https://prove2.me/theorems/2af6265d-3008-4c33-8c7c-fc7babfe33a6
-- title:
--   Lemma 5 — (17) has a unique solution H_ρ iff ρ ∈ σ₀(Q)ᶜ, H_ρ is rational in ρ there, and (18) H_ρ = (I − P*)R_ρ = R_ρ − ρ⁻¹P* = R_ρ(I − P*)
-- statement:
--   Let $P$ be an $S\times S$ substochastic matrix, $Q=P-I$, $P^*$ the Cesàro limit of the powers of $P$, and $\rho$ real.
--
--   1. The systems
--   $$(\rho I-Q)H=I-P^*,\quad P^*H=0,\qquad H(\rho I-Q)=I-P^*,\quad HP^*=0 \tag{17}$$
--   have a unique common solution $H$ if and only if $\rho\in\sigma_0(Q)^c$, that is, $\rho=0$ or $\rho\notin\sigma(Q)$; on $\sigma_0(Q)^c$ the solution is the reduced resolvent $H_\rho$.
--   2. $H_\rho$ has a rational representation in $\rho$ on $\sigma_0(Q)^c$: there are a matrix $N(\rho)$ of polynomials and a polynomial $d(\rho)$, nonzero on $\sigma_0(Q)^c$, with $H_\rho=d(\rho)^{-1}N(\rho)$ there.
--   3. If $\rho\notin\sigma(Q)$, then $\rho^{-1}P^*$ is finite ($\rho\neq0$ or $P^*=0$) and, with $R_\rho=(\rho I-Q)^{-1}$,
--   $$H_\rho=[I-P^*]R_\rho=R_\rho-\rho^{-1}P^*=R_\rho[I-P^*]. \tag{18}$$
--
--   So $R_\rho(Q)=\rho^{-1}P^*+H_\rho$ splits the resolvent into its pole at $\rho=0$ and a part that stays regular there.
--
--   **Formalization Note** The block systems of (17) are written as their four matrix equations (the right-hand block of (17) is printed as a column although it multiplies $H_\rho$ from the right). The paper's "$\rho\in_\sigma(Q)^c$" in (b) is read $\rho\in\sigma(Q)^c$. $\rho$ is real; real $\rho\in\sigma(Q)$ is `ρ ∈ spectrum ℝ (P - 1)`. At $\rho=0$ Lean's $0^{-1}=0$ makes $\rho^{-1}P^*=0$.
-- source:
--   Veinott, Discrete Dynamic Programming with Sensitive Discount Optimality Criteria, Ann. Math. Statist. 40(5):1635–1660 (1969), DOI 10.1214/aoms/1177697379, p. 1642, §3, Lemma 5, (17), (18)

import Mathlib
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_VeinottSensitiveDP_Sensitive_Matrix
open Filter Topology Matrix BlackwellDiscreteDP.NearOne

namespace VeinottSensitiveDP.Sensitive

/-- Lemma 5: let `P` be an `S × S` substochastic matrix, `Q = P − I`, `P* = limitMatrix P`.

(a) For real `ρ`, the two systems (17)
`(ρI − Q)H = I − P*`, `P*H = 0` and `H(ρI − Q) = I − P*`, `HP* = 0`
have a unique common solution `H` if and only if `ρ ε σ₀(Q)ᶜ` (i.e. `ρ = 0` or `ρ ∉ σ(Q)`); that
solution is the reduced resolvent `H_ρ`; and `H_ρ` has a rational representation in `ρ` on
`σ₀(Q)ᶜ`: `H_ρ = d(ρ)⁻¹ N(ρ)` for a polynomial matrix `N` and a polynomial `d` not vanishing on
`σ₀(Q)ᶜ`.

(b) If `ρ ∉ σ(Q)`, then `ρ⁻¹P*` is finite (`ρ ≠ 0` or `P* = 0`) and, with `R_ρ = (ρI − Q)⁻¹`,
(18) `H_ρ = [I − P*]R_ρ = R_ρ − ρ⁻¹P* = R_ρ[I − P*]`.

Veinott, Discrete Dynamic Programming with Sensitive Discount Optimality Criteria,
Ann. Math. Statist. 40(5):1635–1660 (1969), DOI 10.1214/aoms/1177697379, p. 1642, §3, Lemma 5, (17), (18).

**Formalization Note.** The two block systems of (17) are written as their four matrix equations;
the right-hand block of (17) is printed as a column although it multiplies `H_ρ` from the right.
`ρ` is real (complex `ρ` enters only in §5). "`ρ ε_σ (Q)ᶜ`" in (b) is read `ρ ε σ(Q)ᶜ`. In (b),
at `ρ = 0` Lean's `0⁻¹ = 0` makes `ρ⁻¹P* = 0`, consistent with `P* = 0` there. -/
theorem lemma_5 {St : Type} [Fintype St] [DecidableEq St] (P : Matrix St St ℝ)
    (hP : IsSubstochastic P) :
    (∀ ρ : ℝ, (∃! X : Matrix St St ℝ,
        (ρ • (1 : Matrix St St ℝ) - (P - 1)) * X = 1 - limitMatrix P ∧
        limitMatrix P * X = 0 ∧
        X * (ρ • (1 : Matrix St St ℝ) - (P - 1)) = 1 - limitMatrix P ∧
        X * limitMatrix P = 0) ↔ InSigmaZeroCompl ρ (P - 1)) ∧
    (∀ ρ : ℝ, InSigmaZeroCompl ρ (P - 1) →
        (ρ • (1 : Matrix St St ℝ) - (P - 1)) * reducedResolvent P ρ = 1 - limitMatrix P ∧
        limitMatrix P * reducedResolvent P ρ = 0 ∧
        reducedResolvent P ρ * (ρ • (1 : Matrix St St ℝ) - (P - 1)) = 1 - limitMatrix P ∧
        reducedResolvent P ρ * limitMatrix P = 0) ∧
    (∃ (N : Matrix St St (Polynomial ℝ)) (d : Polynomial ℝ), ∀ ρ : ℝ,
        InSigmaZeroCompl ρ (P - 1) →
          d.eval ρ ≠ 0 ∧ reducedResolvent P ρ = (d.eval ρ)⁻¹ • N.map (Polynomial.eval ρ)) ∧
    (∀ ρ : ℝ, ρ ∉ spectrum ℝ (P - 1) →
        (ρ ≠ 0 ∨ limitMatrix P = 0) ∧
        reducedResolvent P ρ = (1 - limitMatrix P) * resolvent ρ (P - 1) ∧
        reducedResolvent P ρ = resolvent ρ (P - 1) - ρ⁻¹ • limitMatrix P ∧
        reducedResolvent P ρ = resolvent ρ (P - 1) * (1 - limitMatrix P)) := by sorry

end VeinottSensitiveDP.Sensitive
