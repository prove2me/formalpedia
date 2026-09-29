-- Prove2me | Theorems.Thm_WLight_exists_analyticOnNhd_div_of_monicRel
-- name    : WLight.exists_analyticOnNhd_div_of_monicRel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/abb58f54-78a6-5d86-b5be-f1cfead2bda8
-- title:
--   Analytic divisibility from a monic relation with G-weighted coefficients
-- statement:
--   Let $\Bbbk$ be a nontrivially normed field and let $U \subseteq \Bbbk$ be a set that is open and preconnected. Let $F, G : \Bbbk \to \Bbbk$, let $c : \mathbb{N} \to (\Bbbk \to \Bbbk)$ be a family of coefficient functions, and let $n$ be a natural number. Assume that $F$ and $G$ are analytic on a neighbourhood of each point of $U$, that $G$ does not vanish identically on $U$ in the strong sense that there exists $z \in U$ with $G z \neq 0$, and that for each index $k < n$ the coefficient function $c_k$ is likewise analytic on a neighbourhood of each point of $U$. Assume finally the monic relation
--   $$F^n + \sum_{k < n} c_k \, G^{\,n-k} F^k = 0$$
--   holds pointwise at every point of $U$, the powers and products being taken in the ring of $\Bbbk$-valued functions. The conclusion is that there exists $H : \Bbbk \to \Bbbk$, analytic on a neighbourhood of each point of $U$, such that $F z = G z \cdot H z$ for all $z \in U$; that is, $G$ divides $F$ in the ring of functions analytic near each point of $U$. Nothing is asserted about behaviour outside or on the boundary of $U$.
--
--   This is the division engine behind arguments showing that a quotient $F/G$ is analytic once the quotient satisfies a monic algebraic relation whose lower coefficients carry compensating powers of $G$: the relation forces the vanishing order of $F$ to dominate that of $G$ at each point of $U$, the preconnectedness hypothesis and the identity principle ruling out identical vanishing of $G$. It is applied through its upper-half-plane counterpart [`WLight.exists_mdifferentiable_div_of_monicRel`](thm.html#WLight.exists_mdifferentiable_div_of_monicRel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WLight_exists_analyticOnNhd_div_of_monicRel.lean

import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.Geometry.Manifold.Notation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open Complex Real UpperHalfPlane
open scoped Manifold MatrixGroups ModularForm

theorem WLight.exists_analyticOnNhd_div_of_monicRel {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {U : Set 𝕜} (hU : IsOpen U) (hUc : IsPreconnected U)
    {F G : 𝕜 → 𝕜} {c : ℕ → 𝕜 → 𝕜} {n : ℕ}
    (hF : AnalyticOnNhd 𝕜 F U) (hG : AnalyticOnNhd 𝕜 G U) (hG0 : ∃ z ∈ U, G z ≠ 0)
    (hc : ∀ k < n, AnalyticOnNhd 𝕜 (c k) U)
    (hrel : Set.EqOn (F ^ n + ∑ k ∈ Finset.range n, c k * G ^ (n - k) * F ^ k) 0 U) :
    ∃ H : 𝕜 → 𝕜, AnalyticOnNhd 𝕜 H U ∧ Set.EqOn F (G * H) U := by sorry
