-- Prove2me | Theorems.Thm_PWDB_lemma_C_8
-- name    : PWDB.lemma_C_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:39:03.567129+00:00
-- url     : https://prove2.me/theorems/f31ef128-bcdb-4254-8035-d4c93eca3951
-- title:
--   Lemma C.8 — recession directions via $0c_\ell(v/0)$
-- statement:
--   Let $F$ be a finite-dimensional real inner product space.
--
--   1. If $c : F \to \overline{\mathbb R}$ is proper, closed and convex, then $v$ is a recession direction of $c$ (that is, $c(z + tv) \le c(z)$ for all $z \in F$ and $t \ge 0$) if and only if $0c(v/0) \le 0$.
--   2. If $c_\ell$, $\ell \in L$, satisfy (C) and $Z = \{z \mid c_\ell(z) \le 0\ \forall \ell\}$ is nonempty, then $v$ is a recession direction of $Z$ (that is, $z + tv \in Z$ for all $z \in Z$, $t \ge 0$) if and only if $0c_\ell(v/0) \le 0$ for all $\ell \in L$.
--
--   Here $0c(v/0) = \delta^*_{\operatorname{dom} c^*}(v)$ is the convex perspective at $t = 0$. The lemma explains the multiplier-zero terms of (D-B′).
--
--   Differences from the source:
--   - generalization: ℝ^{dx}, ℝ^{dz} → finite-dimensional real inner product spaces E, F; reason: every ℝ^d with the dot product is such a space, so the Lean statement specializes to the printed one
--   - encoding: (C): cℓ proper, closed and convex, Z nonempty → TensorAHPE.IsProperClosedConvex (c ℓ) with c extended-valued, hypothesis (Z c).Nonempty; reason: standing assumptions of p.9, stated as binders; same instances
--   - reading: 'recession direction for the function cℓ' → c(z + t v) ≤ c(z) for all z and all t ≥ 0; reason: Rockafellar's definition (Theorem 8.6), which the paper cites; the proof's variant 'for z with cℓ(z) ≤ 0' makes (i) false for c(z) = 1 + z², whose level set {c ≤ 0} is empty
--   - encoding: 0cℓ(v/0) → persp (c ℓ) v 0; reason: Definition A.2 at t = 0
--   - encoding: assertion (i) for the functions cℓ → assertion (i) for every c : F → EReal satisfying (C); reason: each cℓ is such a function; (i) concerns one function at a time
--   - encoding: 'recession direction for the set Z' → z + t v ∈ Z for all z ∈ Z and all t ≥ 0; reason: the standard definition (Rockafellar 1970, §8)
-- source:
--   Zhen, Kuhn & Wiesemann, A Unified Theory of Robust and Distributionally Robust Optimization via the Primal-Worst-Equals-Dual-Best Principle, arXiv:2105.00760v2 (19 Jul 2023), Lemma C.8, pp.69–70

import Mathlib
import Definitions.Def_TensorAHPE_IsProperClosedConvex
import Definitions.Def_PWDB_persp
import Definitions.Def_PWDB_RobustProgram

namespace PWDB

/-- **Lemma C.8 (Recession Directions)** (Zhen, Kuhn & Wiesemann, arXiv:2105.00760v2, Lemma C.8,
p.69): "The following statements hold.
(i) A vector `v ∈ ℝ^{dz}` is a recession direction for the function `cℓ` if and only if
`0cℓ(v/0) ≤ 0`.
(ii) A vector `v ∈ ℝ^{dz}` is a recession direction for the set `Z` if and only if `0cℓ(v/0) ≤ 0`
for all `ℓ ∈ L`."

**Formalization Note** Under (C) (each `cℓ` proper, closed and convex,
`TensorAHPE.IsProperClosedConvex`) and the standing assumption that `Z` is nonempty (p.9).
`0cℓ(v/0)` is the convex perspective at `t = 0`, `persp (c ℓ) v 0` (Definition A.2). A recession
direction of a function `c` is read in Rockafellar's sense, which the paper's proof cites
(Rockafellar 1970, Theorem 8.6): `c(z + t v) ≤ c(z)` for all `z` and all `t ≥ 0`. A recession
direction of the set `Z` is a `v` with `z + t v ∈ Z` for all `z ∈ Z`, `t ≥ 0`. Clause (i) is stated
for one function `c` satisfying (C). -/
theorem lemma_C_8 {F L : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [Fintype L] :
    (∀ (c : F → EReal), TensorAHPE.IsProperClosedConvex c → ∀ v : F,
      ((∀ z : F, ∀ t : ℝ, 0 ≤ t → c (z + t • v) ≤ c z) ↔ persp c v 0 ≤ 0)) ∧
    (∀ (c : L → F → EReal), (∀ ℓ, TensorAHPE.IsProperClosedConvex (c ℓ)) → (Z c).Nonempty →
      ∀ v : F, ((∀ z ∈ Z c, ∀ t : ℝ, 0 ≤ t → z + t • v ∈ Z c) ↔ ∀ ℓ, persp (c ℓ) v 0 ≤ 0)) := by sorry

end PWDB
