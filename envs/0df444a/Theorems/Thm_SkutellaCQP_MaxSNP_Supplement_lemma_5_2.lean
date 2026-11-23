-- Prove2me | Theorems.Thm_SkutellaCQP_MaxSNP_Supplement_lemma_5_2
-- name    : SkutellaCQP.MaxSNP.Supplement.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T09:50:41.802964+00:00
-- url     : https://prove2.me/theorems/c1b492eb-652f-4717-bc4e-0052af777695
-- title:
--   Lemma 5.2 — correlated probability bounds imply the refined SDP expectation bound
-- statement:
--   Let $p_{ij}>0$ and $w_j\ge0$ for $n$ jobs on two unrelated machines without release dates. Let $v,a(v),Z$ be feasible for the full SDP (28)–(31), and let $\mu$ be any probability law on assignments. Suppose $1\le\rho_1\le\rho_2$ and, for both machines and every $j,k$,
--   $$\Pr[j\mapsto i]\le\frac{\rho_1}{2}\left(\frac{1+\langle v_i,v_j\rangle}{2}+\frac{(1+a_{ij})a_{ij}}2\right),$$
--   $$\Pr[j,k\mapsto i]\le\frac{\rho_2}{2}\left(\frac{\langle v_j,v_k\rangle+\langle v_i,v_j\rangle+\langle v_i,v_k\rangle+1}{4}+a_{ij}a_{ik}\right).$$
--   Sequencing each assignment by Smith's order yields both inequalities
--   $$\mathbb E_\mu\sum_jw_jC_j\le\rho_1\frac{3c^Ta(v)}4+\rho_2\left(Z-\frac{3c^Ta(v)}4\right)\le\rho_2Z.$$
--   No independence of assignments is assumed. This bound supports the conditional hyperplane guarantees and the combination with independent rounding.
--
--   Differences from the source:
--   - encoding: machine labels 0 and −1 and finite random assignment → Fin 2 labels and a nonnegative normalized probability weight on all assignments; reason: the same finite joint distribution is represented without measure-theoretic defaults
--   - encoding: the setting and Smith ratio order are inherited from §§1–2 → explicit positive processing times, nonnegative weights, and the published cross-multiplied order; reason: these are exactly the standing assumptions; there is no division by a processing time
-- source:
--   Skutella, Convex quadratic and semidefinite programming relaxations in scheduling, J. ACM 48 (2001), DOI 10.1145/375827.375840, p. 26, Lemma 5.2

import Mathlib
import Definitions.Def_SkutellaCQP_MaxSNP_Supplement_SDP

namespace SkutellaCQP.MaxSNP.Supplement

/-- Lemma 5.2, p. 26: both bounds, for arbitrary correlated assignment laws. -/
theorem lemma_5_2 {n : ℕ} (p : Two → Fin n → ℝ) (w : Fin n → ℝ)
    (hp : ∀ i j, 0 < p i j) (hw : ∀ j, 0 ≤ w j)
    (v : Vectors n) (Z : ℝ) (hv : SDPFeasible p w v Z)
    (μ : (Fin n → Two) → ℝ) (hμ : IsAssignmentLaw μ)
    (ρ₁ ρ₂ : ℝ) (hρ₁ : 1 ≤ ρ₁) (hρ₂ : ρ₁ ≤ ρ₂)
    (hb : ProbabilityBounds v μ ρ₁ ρ₂) :
    expectedValue p w μ ≤ ρ₁ * (3 * linearValue p w v / 4) +
      ρ₂ * (Z - 3 * linearValue p w v / 4) ∧
    ρ₁ * (3 * linearValue p w v / 4) +
      ρ₂ * (Z - 3 * linearValue p w v / 4) ≤ ρ₂ * Z := by sorry

end SkutellaCQP.MaxSNP.Supplement
