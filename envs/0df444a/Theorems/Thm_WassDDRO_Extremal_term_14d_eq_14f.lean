-- Prove2me | Theorems.Thm_WassDDRO_Extremal_term_14d_eq_14f
-- name    : WassDDRO.Extremal.term_14d_eq_14f
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:56:21.391166+00:00
-- url     : https://prove2.me/theorems/e8c29fa8-0ad3-469c-abd2-9885a1435c61
-- title:
--   (14d)–(14f), p. 16 — the ik-th term inf_z ⟨z, q − αξ̂⟩ + α[−ℓ_k + χ_Ξ]*(z) equals αℓ_k(ξ̂ − q/α) − χ_Ξ(ξ̂ − q/α)
-- statement:
--   Assume Assumption 4.1: $\Xi \subseteq E$ is convex and closed, each $-\ell_k$ is proper, convex and lower semicontinuous, and each $\ell_k$ is not identically $-\infty$ on $\Xi$. Fix $k$, a sample point $\hat\xi \in \Xi$, a weight $\alpha \ge 0$ and $q \in E$. Then the $ik$-th term of program (14d),
--   $$\inf_{z}\ \langle z, q - \alpha\hat\xi\rangle + \alpha\,[-\ell_k + \chi_\Xi]^*(z),$$
--   equals the term (14f),
--   $$\alpha\,\ell_k\Big(\hat\xi - \frac{q}{\alpha}\Big) - \chi_\Xi\Big(\hat\xi - \frac{q}{\alpha}\Big),$$
--   read under the conventions of extended arithmetic. Explicitly:
--
--   1. if $\alpha > 0$ and $\hat\xi - q/\alpha \in \Xi$, the term is $\alpha\,\ell_k(\hat\xi - q/\alpha)$;
--   2. if $\alpha > 0$ and $\hat\xi - q/\alpha \notin \Xi$, the term is $-\infty$;
--   3. if $\alpha = 0$ and $q = 0$, the term is $0$;
--   4. if $\alpha = 0$ and $q \ne 0$, the term is $-\infty$.
--
--   This identity, which combines Lemma 4.5 (applied to $f = -\ell_k + \chi_\Xi$) with the paper's conventions $0/0 = 0$ and $q/0 \notin E$ for $q \neq 0$, is what turns (14d) into the explicit program (14g) and then (13).
--
--   **Formalization Note** $[-\ell_k + \chi_\Xi]^*$ is `conjOn Ξ (fun ξ => -ℓ k ξ)`, the supremum restricted to $\Xi$. The four cases are stated separately because $q/0$ has no value in $E$.
-- source:
--   Mohajerin Esfahani & Kuhn, arXiv:1505.05116v3, proof of Theorem 4.4, (14d), (14e), (14f), p. 16

import Mathlib
import Definitions.Def_WassDDRO_Extremal_Setting

namespace WassDDRO.Extremal

/-- (14d)–(14f), p. 16. Under Assumption 4.1, for a sample point ξ̂ ∈ Ξ, a weight α ≥ 0 and
q ∈ E, the ik-th term of (14d), inf_z ⟨z, q − αξ̂⟩ + α[−ℓ_k + χ_Ξ]*(z), equals the term (14f),
α ℓ_k(ξ̂ − q/α) − χ_Ξ(ξ̂ − q/α), read with the conventions of extended arithmetic:
α ℓ_k(ξ̂ − q/α) if α > 0 and ξ̂ − q/α ∈ Ξ; −∞ if α > 0 and ξ̂ − q/α ∉ Ξ; 0 if α = 0 and q = 0;
−∞ if α = 0 and q ≠ 0. -/
theorem term_14d_eq_14f {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {K : ℕ} (Ξ : Set E) (ℓ : Fin K → E → EReal) (hA : Assumption41 Ξ ℓ)
    (k : Fin K) (ξh : E) (hξh : ξh ∈ Ξ) (q : E) (α : ℝ) (hα : 0 ≤ α) :
    let F := ⨅ z : StrongDual ℝ E,
      ((z (q - α • ξh) : ℝ) : EReal) + (α : EReal) * conjOn Ξ (fun ξ => -ℓ k ξ) z
    (0 < α → ξh - α⁻¹ • q ∈ Ξ → F = (α : EReal) * ℓ k (ξh - α⁻¹ • q)) ∧
    (0 < α → ξh - α⁻¹ • q ∉ Ξ → F = ⊥) ∧
    (α = 0 → q = 0 → F = 0) ∧
    (α = 0 → q ≠ 0 → F = ⊥) := by sorry

end WassDDRO.Extremal
