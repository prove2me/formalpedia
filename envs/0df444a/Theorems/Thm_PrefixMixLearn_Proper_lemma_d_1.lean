-- Prove2me | Theorems.Thm_PrefixMixLearn_Proper_lemma_d_1
-- name    : PrefixMixLearn.Proper.lemma_d_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:45:37.844007+00:00
-- url     : https://prove2.me/theorems/a847db5e-fe03-4168-b41c-ef925cb21c7d
-- title:
--   Lemma D.1 — signed product profiles on a common path: positive prefix masses and profile error O(D)
-- statement:
--   Let $Q=Q_\mu$ be a full-support product on $\{0,1\}^d$ ($0<\mu_i<1$) and $F$ a finite signed measure on that space, not necessarily of total mass one, and put $D=\sum_x|F(x)-Q(x)|$. If $D\le1/256$, there is an event $G$ with $Q(G)\ge31/32$ such that on every $x\in G$ all prefix masses $F[x_{\le t}]$, $0\le t\le d$, are positive and
--   $$\max_{0\le t\le d}\Big|\frac{F[x_{\le t}]}{Q[x_{\le t}]}-1\Big|\le64D,\qquad\Big\|\Big(\frac{F[x_{<i}1]}{F[x_{<i}]}-\mu_i\Big)_{i=1}^d\Big\|_2\le\frac{256\sqrt e}{3}D.$$
--   The empty-prefix mass of $F$ is its total mass; the child-to-parent ratios are signed and may leave $[0,1]$. This is the signed-measure trajectory lemma behind the joint unmixing.
--
--   Differences from the source:
--   - encoding: Q = Q_μ any full-support product → μ with 0 < μ_i < 1 for all i; reason: Q_μ has full support exactly when every μ_i ∈ (0,1)
--   - encoding: coordinates i = 1, …, T; laws on {0,1}^T → `Fin T`, coordinate i ↦ i.val + 1; laws are real functions on `Fin T → Bool` with `IsLaw`; reason: Lean convention; same statement
-- source:
--   Saravanan, Proper Agnostic Learning of Two Balanced Product Distributions from Prefix-Conditional Samples, STOC 2027 submission (manuscript sha256 9c359910…), p. 29–30 (PDF 31–32), Lemma D.1, (D.1)

import Mathlib
import Definitions.Def_PrefixMixLearn_Proper_Laws

namespace PrefixMixLearn.Proper

/-- Lemma D.1 (signed product profiles on a common path): for a full-support product `Q = Q_μ` on
`{0,1}^d` and a finite signed measure `F` with `D = Σ_x |F(x) − Q(x)| ≤ 1/256`, there is an event
`G` with `Q(G) ≥ 31/32` on which every prefix mass `F[x_{≤t}]` is positive,
`max_t |F[x_{≤t}]/Q[x_{≤t}] − 1| ≤ 64D` and
`‖(F[x_{<i}1]/F[x_{<i}] − μ_i)_i‖₂ ≤ (256√e/3) D`. -/
theorem lemma_d_1 (d : ℕ) (μ : Fin d → ℝ) (hμ : ∀ i, 0 < μ i ∧ μ i < 1) (F : Cube d → ℝ)
    (hD : ∑ x, |F x - prodLaw μ x| ≤ 1 / 256) :
    ∃ G : Set (Cube d), 31 / 32 ≤ massOf (prodLaw μ) G ∧
      ∀ x ∈ G,
        (∀ t : ℕ, t ≤ d → 0 < prefMass F x t) ∧
        (∀ t : ℕ, t ≤ d →
          |prefMass F x t / prefMass (prodLaw μ) x t - 1| ≤ 64 * ∑ y, |F y - prodLaw μ y|) ∧
        l2 (fun i => condOne F x i - μ i) ≤
          256 * Real.sqrt (Real.exp 1) / 3 * ∑ y, |F y - prodLaw μ y| := by sorry

end PrefixMixLearn.Proper
