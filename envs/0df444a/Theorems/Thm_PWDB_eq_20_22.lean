-- Prove2me | Theorems.Thm_PWDB_eq_20_22
-- name    : PWDB.eq_20_22
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:39:15.897595+00:00
-- url     : https://prove2.me/theorems/a643b43d-f863-4447-9245-8e704415357f
-- title:
--   Eqs. (20)–(22) — the worst-case functions $F_i$ and their conjugates (attained infimum)
-- statement:
--   Let $E, F$ be finite-dimensional real inner product spaces, $c_\ell$ satisfy (C), and $Z = \{z \mid c_\ell(z) \le 0\ \forall \ell\}$ be nonempty and bounded. Let $g : E \times F \to \mathbb R$ satisfy (RF) and $G(x) = \sup_{z \in Z} g(x, z)$. Then
--
--   1. $G$ is proper, closed and convex, and $G(x) < +\infty$ for every $x$;
--   2. for every $w \in E$ and $\lambda \ge 0$,
--   $$
--   \lambda G^*(w/\lambda) = \inf_{z \in Z} \lambda g^{*1}(w/\lambda, z), \tag{22}
--   $$
--   and the infimum is attained by some $z \in Z$.
--
--   With $G = F_i$ this rewrites the dual (21) of (20) as the dual best problem (D-B).
--
--   Differences from the source:
--   - generalization: ℝ^{dx}, ℝ^{dz} → finite-dimensional real inner product spaces E, F; reason: every ℝ^d with the dot product is such a space, so the Lean statement specializes to the printed one
--   - encoding: (RF): fi(·, z) proper closed convex, −fi(x, ·) proper closed convex → fi : E → F → ℝ real-valued with IsRF (convex in x, concave in z); reason: p.8 proves (RF) forces real values; a real-valued convex function on a finite-dimensional space is continuous, hence proper and closed; same instances
--   - encoding: (C): cℓ proper, closed and convex, Z nonempty → TensorAHPE.IsProperClosedConvex (c ℓ) with c extended-valued, hypothesis (Z c).Nonempty; reason: standing assumptions of p.9, stated as binders; same instances
--   - encoding: convex perspective on ℝ^{dx} × ℝ₊ (Definitions A.2, A.4) → persp/pPersp with value +∞ for t < 0; reason: every multiplier in the paper is ≥ 0; no value at t ≥ 0 changes
--   - generalization: (22) as an equality of an infimum, for the functions fi, i ∈ I → (22) for every (RF) function g (covering f0 and every fi), plus attainment of the infimum over Z; reason: attainment holds because z ↦ g∗1(w/λ, z) is lower semicontinuous and Z is compact; it implies the printed equality
--   - encoding: Z compact → Z nonempty and bounded, with (C); reason: (C) makes Z closed (p.9), so on a finite-dimensional space bounded means compact; same instances
-- source:
--   Zhen, Kuhn & Wiesemann, A Unified Theory of Robust and Distributionally Robust Optimization via the Primal-Worst-Equals-Dual-Best Principle, arXiv:2105.00760v2 (19 Jul 2023), proof of Theorem 7 (ii), eqs. (20)–(22), p.54

import Mathlib
import Definitions.Def_TensorAHPE_IsProperClosedConvex
import Definitions.Def_PWDB_IsRF
import Definitions.Def_PWDB_conj
import Definitions.Def_PWDB_persp
import Definitions.Def_PWDB_PartialConj
import Definitions.Def_PWDB_pPersp
import Definitions.Def_PWDB_RobustProgram

namespace PWDB

/-- **Eqs. (20)–(22): the worst-case functions `Fi` and their conjugates** (Zhen, Kuhn & Wiesemann,
arXiv:2105.00760v2, proof of Theorem 7 (ii), p.54): "where `Fi(x) = sup_{zi∈Z} fi(x, zi)`
constitutes a pointwise maximum of convex functions and is therefore convex. Moreover, as `Z` is
compact and `fi(x, zi)` is continuous in `zi` for every `x`, `Fi(x)` is indeed finite for every
`x`, i.e., `dom(Fi) = ℝ^{dx}`. As any finite-valued convex function is continuous, we may thus
conclude that `Fi` is proper, closed and convex." and "To this end, we will show that
`λi Fi∗(wi/λi) = inf_{zi∈Z} λi fi∗1(wi/λi, zi)` (22) for any fixed `λi ≥ 0` and `wi ∈ ℝ^{dx}`."

For `Z` nonempty and bounded and every `g` satisfying (RF), with `G(x) = sup_{z∈Z} g(x, z)`:
1. `G` is proper, closed and convex;
2. `G(x) < +∞` for every `x`;
3. for every `w` and `λ ≥ 0`, `λ G∗(w/λ) = inf_{z∈Z} λ g∗1(w/λ, z)`, and the infimum is attained.

**Formalization Note** (C) is `TensorAHPE.IsProperClosedConvex (c ℓ)`; `Z` is nonempty (standing,
p.9) and bounded (the hypothesis of Theorem 7 (i), (ii); with (C) it is compact). (RF) is `IsRF`.
`λ G∗(w/λ)` is the convex perspective `persp (conj G) w λ` and `λ g∗1(w/λ, z)` the partial
perspective `pPersp (pconj1 g) w λ z` (Definitions A.2, A.4). The infimum is in `EReal`. The
attainment of the infimum is added to (22); it holds because `z ↦ g∗1(w/λ, z)` is lower
semicontinuous and `Z` is compact, and it is how (D-B) inherits solvability in Theorem 7 (i). The
identity is stated for an arbitrary (RF) function `g`, which covers `f0` and every `fi`. -/
theorem eq_20_22 {E F L : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [Fintype L]
    (c : L → F → EReal) (hc : ∀ ℓ, TensorAHPE.IsProperClosedConvex (c ℓ)) (hZ : (Z c).Nonempty)
    (hZb : Bornology.IsBounded (Z c)) (g : E → F → ℝ) (hg : IsRF g) :
    TensorAHPE.IsProperClosedConvex (worst c g) ∧ (∀ x, worst c g x ≠ ⊤) ∧
    ∀ (w : E) (t : ℝ), 0 ≤ t →
      persp (conj (worst c g)) w t =
          ⨅ z ∈ Z c, pPersp (pconj1 (fun x z => ((g x z : ℝ) : EReal))) w t z ∧
        ∃ z ∈ Z c, persp (conj (worst c g)) w t =
          pPersp (pconj1 (fun x z => ((g x z : ℝ) : EReal))) w t z := by sorry

end PWDB
