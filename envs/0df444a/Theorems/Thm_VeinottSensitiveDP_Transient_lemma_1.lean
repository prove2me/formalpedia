-- Prove2me | Theorems.Thm_VeinottSensitiveDP_Transient_lemma_1
-- name    : VeinottSensitiveDP.Transient.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:50:14.653982+00:00
-- url     : https://prove2.me/theorems/5dd100c8-5f20-45c3-9b3c-1f6e35066977
-- title:
--   Lemma 1 — V(π) − V(π*) = Σ Pᴺ(π)v(g_{N+1}, π*) for transient π, π*; and V(g^∞) − V(π*) = [I − P(g)]⁻¹v(g, π*)
-- statement:
--   Consider a dynamic program with finitely many states, finite action sets and nonnegative transition weights (§2 of Veinott 1969), and let $\pi=(g_1,g_2,\dots)$ and $\pi^*$ be transient policies. With $v(g,\pi^*)=V(g,\pi^*)-V(\pi^*)$,
--
--   $$V(\pi)-V(\pi^*)=\sum_{N=0}^\infty P^N(\pi)\,v(g_{N+1},\pi^*).\tag{2}$$
--
--   If moreover $\pi=g^\infty$ is stationary, then $I-P(g)$ is nonsingular and
--
--   $$V(g^\infty)-V(\pi^*)=[I-P(g)]^{-1}\,v(g,\pi^*).\tag{3}$$
--
--   The lemma expresses the difference of two total returns through the one-step comparisons $v(\cdot,\pi^*)$, generalizing a result of Howard from stationary to nonstationary policies. It is the basis of policy improvement in this model.
--
--   **Formalization Note.** Policies are indexed from $0$, so $g_{N+1}$ is `π N`. $[I-P(g)]^{-1}$ is Mathlib's matrix inverse, which is $0$ for a singular matrix; nonsingularity for transient $g^\infty$ is part of the claim, not a hypothesis.
-- source:
--   Veinott, Discrete Dynamic Programming with Sensitive Discount Optimality Criteria, Ann. Math. Statist. 40(5):1635–1660 (1969), DOI 10.1214/aoms/1177697379, p. 1637, Lemma 1

import Mathlib
import Definitions.Def_VeinottSensitiveDP_Transient_Model

namespace VeinottSensitiveDP.Transient

open Matrix

variable {St : Type} [Fintype St] [DecidableEq St] [Nonempty St] {A : St → Type}
  [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)] [∀ s, Nonempty (A s)]

/-- **Lemma 1** (Veinott, *Discrete Dynamic Programming with Sensitive Discount Optimality Criteria*,
Ann. Math. Statist. 40(5):1635–1660 (1969), DOI 10.1214/aoms/1177697379, p. 1637).
If `π = (gᵢ)` and `π* ≡ (fᵢ)` are transient, then
(2) `V(π) − V(π*) = Σ_{N=0}^∞ Pᴺ(π) v(g_{N+1}, π*)`, where `v(g, π*) ≡ V(g, π*) − V(π*)`.
If also `π = g^∞`, then (3) `V(g^∞) − V(π*) = [I − P(g)]⁻¹ v(g, π*)`.

**Formalization Note.** With `π 0 = g₁`, the summand `Pᴺ(π) v(g_{N+1}, π*)` is
`PN N π *ᵥ v (π N) π*`. The sum is `tsum` in `St → ℝ`. `[I − P(g)]⁻¹` is Mathlib's matrix
inverse (which would be `0` for a singular matrix); its nonsingularity for transient `g^∞` is
part of what (3) asserts, so it is not assumed. -/
theorem lemma_1 (D : Program St A) (π πs : Policy St A)
    (hπ : D.IsTransient π) (hπs : D.IsTransient πs) :
    D.V π - D.V πs = ∑' N, D.PN N π *ᵥ D.v (π N) πs ∧
    ∀ g : DecisionRule St A, π = stationary g →
      D.V (stationary g) - D.V πs = (1 - D.Pmat g)⁻¹ *ᵥ D.v g πs := by sorry

end VeinottSensitiveDP.Transient
