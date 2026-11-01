-- Prove2me | Theorems.Thm_PConeEB_lemma_4_3
-- name    : PConeEB.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:33:56.100733+00:00
-- url     : https://prove2.me/theorems/d628fc02-ae59-4ff2-95e4-4e90f63f4aa0
-- title:
--   Lemma 4.3 — a curve of order $1/2$ when $|J_z|\ge2$
-- statement:
--   Let $n\ge2$, $p,q\in(1,\infty)$ with $\frac1p+\frac1q=1$, and $z\in\partial\mathcal K_q^{n+1}\setminus\{0\}$ with $|J_z|\ge2$. Let $\mathcal F_z:=\{z\}^\perp\cap\mathcal K_p^{n+1}$ and let $f\in\mathcal F_z\setminus\{0\}$ be as in (4.5). Then there is a continuous function $w:(0,1]\to\{z\}^\perp\setminus\mathcal F_z$ with
--   $$
--   \lim_{\epsilon\downarrow0}w_\epsilon=f\qquad\text{and}\qquad\limsup_{\epsilon\downarrow0}\frac{\operatorname{dist}(w_\epsilon,\mathcal K_p^{n+1})^{1/2}}{\operatorname{dist}(w_\epsilon,\mathcal F_z)}<\infty.
--   $$
--
--   The curve shows that no exponent above $\frac12$ can hold at a face with at least two nonzero entries in $\bar z$.
--
--   Differences from the source:
--   - encoding: w_ε ∈ {z}^⊥ \ F_z → SatisfiesG1, which also records w ε ∈ span K; reason: the p-cone is full-dimensional, so the extra clause is automatic
--   - encoding: (G1): w : (0, 1] → {z}^⊥ ∩ span K \ F continuous, L_g = limsup < ∞ → SatisfiesG1 with a total w, the conditions on Set.Ioc 0 1, and an ENNReal limsup equal to ENNReal.ofReal Lg with 0 ≤ Lg; reason: Lean conventions; same instances, and an ENNReal limsup has no boundedness side condition
--   - encoding: ℝ^{n+1}, x₀, x̄, ‖x̄‖_p, ∂ → RR n = EuclideanSpace ℝ (Fin (n + 1)), x 0, x i.succ for i : Fin n, pNorm with real rpow, frontier; reason: Lean conventions; same instances
-- source:
--   Lindstrom, Lourenço & Pong, Optimal error bounds in the absence of constraint qualifications, arXiv:2109.11729v4, Lemma 4.3, p.22

import Mathlib
import Definitions.Def_PConeEB_Jz
import Definitions.Def_PConeEB_pCone
import Definitions.Def_PConeEB_facialVec
import Definitions.Def_PConeEB_SatisfiesG1

namespace PConeEB

/-- Lemma 4.3. Let `n ≥ 2`, `1/p + 1/q = 1`, `z ∈ ∂K_q^{n+1} \ {0}` with `|J_z| ≥ 2`, and let `f` be
as in (4.5). There is a continuous `w : (0, 1] → {z}^⊥ \ F_z` with `w_ε → f` and
`limsup_{ε ↓ 0} dist(w_ε, K_p^{n+1})^{1/2} / dist(w_ε, F_z) < ∞`.
Lindstrom, Lourenço & Pong, arXiv:2109.11729v4, Lemma 4.3, p.22.

**Formalization Note.** Stated as `SatisfiesG1` with `g = |·|^{1/2}` and `v = f`. The clause
`w ε ∈ span K` in `SatisfiesG1` is automatic here, since the `p`-cone is full-dimensional. -/
theorem lemma_4_3 {n : ℕ} (hn : 2 ≤ n) {p q : ℝ} (hp : 1 < p) (hpq : 1 / p + 1 / q = 1)
    {z : RR n} (hz : z ∈ frontier (pCone n q)) (hz0 : z ≠ 0)
    (hJ : 2 ≤ (Jz z).card) :
    ∃ (w : ℝ → RR n) (Lg : ℝ),
      SatisfiesG1 (pCone n p) z (fun t => |t| ^ (1 / 2 : ℝ)) (facialVec q z) w Lg := by sorry

end PConeEB
