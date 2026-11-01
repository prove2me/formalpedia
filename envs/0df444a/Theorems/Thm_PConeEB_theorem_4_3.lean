-- Prove2me | Theorems.Thm_PConeEB_theorem_4_3
-- name    : PConeEB.theorem_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:34:27.286607+00:00
-- url     : https://prove2.me/theorems/bafdfff2-c95b-4e22-8473-a9664560968d
-- title:
--   Theorem 4.3 — error bounds for the $p$-cone and their optimality
-- statement:
--   Let $n\ge2$, $p\in(1,\infty)$, and let $q$ satisfy $\frac1p+\frac1q=1$. Let $\mathcal L\subseteq\mathbb R^{n+1}$ be a subspace and $a\in\mathbb R^{n+1}$ with $(\mathcal L+a)\cap\mathcal K_p^{n+1}\ne\emptyset$. Then:
--
--   1. If $(\mathcal L+a)\cap\mathcal K_p^{n+1}=\{0\}$ or $(\mathcal L+a)\cap\operatorname{ri}\mathcal K_p^{n+1}\ne\emptyset$, then $\mathcal K_p^{n+1}$ and $\mathcal L+a$ satisfy a Lipschitzian error bound.
--   2. Otherwise, there is $z\in\partial\mathcal K_q^{n+1}\cap\mathcal L^\perp\cap\{a\}^\perp$ with $z\ne0$, and for every such $z$, $\mathcal K_p^{n+1}$ and $\mathcal L+a$ satisfy a uniform Hölderian error bound with exponent $\alpha_z\ge\min\{\frac12,\frac1p\}$, where $\alpha_z$ is as in (4.6).
--
--   Furthermore, the error bound in item 2 is optimal in the following sense. For every $z\in\partial\mathcal K_q^{n+1}\setminus\{0\}$, taking $\mathcal L=\{z\}^\perp$ and $a=0$: for any consistent error bound function $\Phi$ for $\mathcal K_p^{n+1}$ and $\{z\}^\perp$ and any $\hat\eta>0$, there are constants $\hat\kappa>0$ and $s_0>0$ such that
--   $$
--   s^{\alpha_z}\le\hat\kappa\,\Phi(\hat\kappa s,\hat\eta)\qquad\forall s\in[0,s_0].
--   $$
--   In particular, $\mathcal K_p^{n+1}$ and $\{z\}^\perp$ do not satisfy a uniform Hölderian error bound with exponent $\hat\alpha$ satisfying $\alpha_z<\hat\alpha\le1$.
--
--   The theorem determines the sharp Hölderian error bound for conic feasibility over every $p$-cone, with no constraint qualification. The exponent depends on the zero pattern of $z$, and it refutes the conjecture that the exponent is $\frac1p$ for every $p$-cone.
--
--   Differences from the source:
--   - reading: item (ii) names z with no quantifier → there is such a z, and every such z gives the bound; reason: this implies both the "some z" and the "every z" reading; the proof uses only z ∈ ∂K_q \ {0} ∩ L^⊥ ∩ {a}^⊥
--   - reading: "If L = {z}^⊥, a = 0" with the z of item (ii) → the optimality clause for every z ∈ ∂K_q \ {0}; reason: for such L and a, item (ii) applies with this z, so the clause loses nothing and is not limited to one z
--   - encoding: the "In particular" sentence and the two items, "ri", q fixed by 1/q + 1/p = 1 → one theorem, intrinsicInterior ℝ, a parameter q with hypothesis 1 / p + 1 / q = 1; reason: Lean conventions; together with 1 < p the equation forces 1 < q
--   - encoding: ℝ^{n+1}, x₀, x̄, ‖x̄‖_p, ∂ → RR n = EuclideanSpace ℝ (Fin (n + 1)), x 0, x i.succ for i : Fin n, pNorm with real rpow, frontier; reason: Lean conventions; same instances
-- source:
--   Lindstrom, Lourenço & Pong, Optimal error bounds in the absence of constraint qualifications, arXiv:2109.11729v4, Theorem 4.3, p.26

import Mathlib
import Definitions.Def_PConeEB_affineSet
import Definitions.Def_PConeEB_hyperplane
import Definitions.Def_PConeEB_IsUniformHolderianEB
import Definitions.Def_PConeEB_IsConsistentEBF
import Definitions.Def_PConeEB_pCone
import Definitions.Def_PConeEB_alphaZ

namespace PConeEB

/-- Theorem 4.3 (error bounds for the `p`-cone and their optimality). Let `n ≥ 2`, `p ∈ (1, ∞)`,
`1/p + 1/q = 1`, and `L`, `a` with `(L + a) ∩ K_p^{n+1} ≠ ∅`.
(i) If `(L + a) ∩ K_p^{n+1} = {0}` or `(L + a) ∩ ri K_p^{n+1} ≠ ∅`, then `K_p^{n+1}` and `L + a` satisfy
a Lipschitzian error bound.
(ii) Otherwise there is `z ∈ ∂K_q^{n+1} ∩ L^⊥ ∩ {a}^⊥` with `z ≠ 0`, and for every such `z`,
`K_p^{n+1}` and `L + a` satisfy a uniform Hölderian error bound with exponent
`α_z ≥ min{1/2, 1/p}`, where `α_z` is as in (4.6).
Optimality: for every `z ∈ ∂K_q^{n+1} \ {0}`, every consistent error bound function `Φ` for
`K_p^{n+1}` and `{z}^⊥` and every `η̂ > 0`, there are `κ̂, s₀ > 0` with `s^{α_z} ≤ κ̂ Φ(κ̂ s, η̂)` for
`s ∈ [0, s₀]`; and `K_p^{n+1}` and `{z}^⊥` satisfy no uniform Hölderian error bound with exponent `α̂`,
`α_z < α̂ ≤ 1`. Lindstrom, Lourenço & Pong, arXiv:2109.11729v4, Theorem 4.3, p.26.

**Formalization Note.** The `z` of (ii) carries no printed quantifier. The statement asserts both
that it exists and that every such `z` works. `ri` is `intrinsicInterior ℝ`, and `∂` is `frontier`.
`q` is a parameter fixed by `1/p + 1/q = 1`, and this equation with `1 < p` forces `1 < q`. -/
theorem theorem_4_3 {n : ℕ} (hn : 2 ≤ n) {p q : ℝ} (hp : 1 < p) (hpq : 1 / p + 1 / q = 1) :
    (∀ (L : Submodule ℝ (RR n)) (a : RR n), (affineSet L a ∩ pCone n p).Nonempty →
      ((affineSet L a ∩ pCone n p = {0} ∨
          (affineSet L a ∩ intrinsicInterior ℝ (pCone n p)).Nonempty) →
        IsUniformHolderianEB (pCone n p) (affineSet L a) 1) ∧
      (¬ (affineSet L a ∩ pCone n p = {0} ∨
          (affineSet L a ∩ intrinsicInterior ℝ (pCone n p)).Nonempty) →
        (∃ z : RR n, z ∈ frontier (pCone n q) ∧ z ≠ 0 ∧ z ∈ Lᗮ ∧ inner ℝ z a = 0) ∧
        ∀ z : RR n, z ∈ frontier (pCone n q) → z ≠ 0 → z ∈ Lᗮ → inner ℝ z a = 0 →
          IsUniformHolderianEB (pCone n p) (affineSet L a) (alphaZ p z) ∧
            min (1 / 2) (1 / p) ≤ alphaZ p z)) ∧
    (∀ z : RR n, z ∈ frontier (pCone n q) → z ≠ 0 →
      (∀ Φ : ℝ → ℝ → ℝ, IsConsistentEBF ![pCone n p, hyperplane z] Φ →
        ∀ ηhat : ℝ, 0 < ηhat →
          ∃ κhat : ℝ, 0 < κhat ∧ ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ s ∈ Set.Icc 0 s₀,
            s ^ alphaZ p z ≤ κhat * Φ (κhat * s) ηhat) ∧
      ∀ αhat : ℝ, alphaZ p z < αhat → αhat ≤ 1 →
        ¬ IsUniformHolderianEB (pCone n p) (hyperplane z) αhat) := by sorry

end PConeEB
