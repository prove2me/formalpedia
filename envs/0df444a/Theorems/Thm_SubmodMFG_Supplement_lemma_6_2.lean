-- Prove2me | Theorems.Thm_SubmodMFG_Supplement_lemma_6_2
-- name    : SubmodMFG.Supplement.lemma_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T01:26:36.281041+00:00
-- url     : https://prove2.me/theorems/9165db4f-a1ce-4e42-8824-ed69e0d72689
-- title:
--   Lemma 6.2 (corrected: convex nonempty control set) — optimal relaxed controls exist, and strict controls dominate relaxed ones
-- statement:
--   In the reflected MFG of §6 (state confined to $[0,M]$ by a reflection $v$, relaxed controls $\lambda$ with values in $\mathcal P(A)$, cost $J(\rho,\mu)=E^P\big[\int_0^T(f(t,X_t,\mu_t)+\int_Al(t,X_t,a)\lambda_t(da))dt+g(X_T,\mu_T)+\int_0^Tc_t\,d|v|_t\big]$), with $A$ compact, nonempty and convex:
--
--   1. For every $\mu\in L_M$ there is an admissible relaxed control minimizing $J(\cdot,\mu)$; equivalently $\arg\min_EJ(\cdot,\mu)\neq\emptyset$.
--   2. For every relaxed control $\rho=(\Omega,\mathcal F,\mathbb F,P,W,\lambda,v,X)$ there is a strict control $\hat\rho=(\Omega,\mathcal F,\mathbb F,P,W,\hat\lambda,v,X)$ on the same basis, with the same reflection and state, such that $J(\hat\rho,\mu)\le J(\rho,\mu)$ for every $\mu\in L_M$.
--
--   Part 2 lets the relaxed fixed points of (6.4) be turned into equilibria of Definition 6.1 in strict controls.
--
--   **Formalization Note** A relaxed control is a stochastic basis together with the processes $(\lambda,v,X)$ on it; part 2 keeps the basis, $v$ and $X$.
--
--   Differences from the source:
--   - correction: a compact control set A ⊂ ℝ → A compact, nonempty and convex; reason: for A = {0, 1}, λ_t = (δ₀ + δ₁)/2 has mean 1/2 ∉ A; a strict control with the same X, v, W would need drift α_t = 1/2 dt-a.e., so (2) fails; for A = ∅ there are no controls (P(∅) = ∅) and (1) fails (DISPROOF.md). With A convex, α_t = ∫ a λ_t(da) ∈ A as in the paper's proof
--   - reading: σ (not restated in §6) → a constant σ ≥ 0; reason: as in §5.2.1, whose model §6 adapts
--   - encoding: (6.1) 'for any t ∈ [0, T], P-a.s.'; |v| the total variation → for each t a.s.; v with right-continuous paths of bounded variation and d|v| the Stieltjes measure of its variation; reason: d|v| requires bounded variation
-- source:
--   Dianetti, Ferrari, Fischer, Nendel, A Unifying Framework for Submodular Mean Field Games, arXiv:2201.07850v1, §6.2, Lemma 6.2, p.26 (proof p.27)

import Mathlib
import Definitions.Def_SubmodMFG_Supplement_SubProb
import Definitions.Def_RepairSched_UsualConditions
import Definitions.Def_SubmodMFG_Supplement_Processes
import Definitions.Def_SubmodMFG_Supplement_SingularCommon
import Definitions.Def_SubmodMFG_Supplement_ReflectedMFG

namespace SubmodMFG.Supplement

/-- **Lemma 6.2** — optimal relaxed controls exist, and every relaxed control is dominated by a
strict control with the same state and reflection.
Dianetti, Ferrari, Fischer, Nendel, *A Unifying Framework for Submodular Mean Field Games*,
arXiv:2201.07850v1, §6.2, Lemma 6.2, p.26: "(1) For any µ ∈ L_M, the set arg min_E J(·, µ) is
nonempty. (2) If ρ = (Ω, 𝓕, 𝔽, P, W, X, λ, v) ∈ E_w, there exists a control
ρ̂ = (Ω, 𝓕, 𝔽, P, W, X, λ̂, v) ∈ E_{w,s} such that J(ρ̂, µ) ≤ J(ρ, µ), for any µ ∈ L_M."

**Formalization Note.** Standing assumptions of §6 (`ReflModel.Standing`, with `A` convex).
(1): `J_E(ν^ρ, µ) = J(ρ, µ)`, so a minimizing control rule is the rule of an optimal relaxed
control. (2): `ρ̂` lives on the same basis `(Ω, 𝓕, 𝔽, P, W)` with the same `v` and `X`. -/
theorem lemma_6_2 (D : ReflModel) (hD : D.Standing) :
    (∀ μ : D.LM, ∃ ρ : D.Ctrl, D.IsOptimal ρ μ.1) ∧
    (∀ (β : D.Basis) (ρ : D.CtrlOn β), ∃ ρ' : D.CtrlOn β, ρ'.v = ρ.v ∧ ρ'.X = ρ.X ∧
      D.IsStrict ⟨β, ρ'⟩ ∧ ∀ μ : D.LM, D.J ⟨β, ρ'⟩ μ.1 ≤ D.J ⟨β, ρ⟩ μ.1) := by sorry

end SubmodMFG.Supplement
