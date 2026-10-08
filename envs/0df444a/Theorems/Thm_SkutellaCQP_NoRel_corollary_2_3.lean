-- Prove2me | Theorems.Thm_SkutellaCQP_NoRel_corollary_2_3
-- name    : SkutellaCQP.NoRel.corollary_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:06:16.463981+00:00
-- url     : https://prove2.me/theorems/1bb75f13-1355-4c73-9051-be23f0b8afe5
-- title:
--   Corollary 2.3, p. 9 — (IQP) and (QP) have equal optima; rounding an optimal ā inside its support is optimal
-- statement:
--   The optimal values of (IQP) and (QP) are equal. Precisely, with $\mathrm{val}(\sigma)=\sum_jw_jC_j(\sigma)$ the value of an assignment $\sigma$ sequenced by Smith's order:
--
--   1. for every feasible $a$ of (QP) there is an assignment $\sigma$ with $\mathrm{val}(\sigma)\le Z_{QP}(a)$;
--   2. for every assignment $\sigma$, its $0/1$ vector $a^\sigma$ ($a^\sigma_{ij}=1$ iff $\sigma(j)=i$) has $Z_{QP}(a^\sigma)=\mathrm{val}(\sigma)$.
--
--   Moreover, if $\bar a$ is an optimum solution of (QP), then every assignment $\sigma$ that sends each job $j$ to a machine $i$ with $\bar a_{ij}>0$ is an optimal schedule:
--   $$
--   \mathrm{val}(\sigma)\le\mathrm{val}(\tau)\qquad\text{for every assignment }\tau .
--   $$
--
--   Consequently solving (QP) is as hard as $R\,|\,|\sum w_jC_j$ itself, which motivates the convexification of §2.2.
--
--   **Formalization Note** "Optimal values are equal" is stated as the two inequalities 1 and 2, which do not presuppose that either optimum exists. "$\bar a$ is an optimum solution to (QP)" is the hypothesis that $\bar a$ is feasible and $Z_{QP}(\bar a)\le Z_{QP}(a')$ for every feasible $a'$. The standing assumptions $p_{ij}>0$, $w_j\ge 0$ are hypotheses.
-- source:
--   Skutella, Convex quadratic and semidefinite programming relaxations in scheduling, J. ACM 48 (2001), p. 9, Corollary 2.3

import Mathlib
import Definitions.Def_SkutellaCQP_NoRel_Setting

namespace SkutellaCQP.NoRel

/-- Corollary 2.3 (p. 9). The optimal values of (IQP) and (QP) coincide: every feasible `a` of (QP)
is matched by an assignment of no larger value, and every assignment has `Z_QP` equal to its value.
Moreover, if `a` is optimal for (QP), every assignment that sends each job `j` to a machine `i` with
`a_ij > 0` is an optimal schedule. -/
theorem corollary_2_3 {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ)
    (hp : ∀ i j, 0 < p i j) (hw : ∀ j, 0 ≤ w j) :
    ((∀ a : Fin m → Fin n → ℝ, Feasible a → ∃ σ : Fin n → Fin m, val p w σ ≤ ZQP p w a) ∧
      ∀ σ : Fin n → Fin m, ZQP p w (ind σ) = val p w σ) ∧
    ∀ a : Fin m → Fin n → ℝ, Feasible a →
      (∀ b : Fin m → Fin n → ℝ, Feasible b → ZQP p w a ≤ ZQP p w b) →
      ∀ σ : Fin n → Fin m, (∀ j, 0 < a (σ j) j) → ∀ τ : Fin n → Fin m, val p w σ ≤ val p w τ := by sorry

end SkutellaCQP.NoRel
