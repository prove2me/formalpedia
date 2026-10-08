-- Prove2me | Theorems.Thm_SkutellaCQP_MaxCut_eq_37
-- name    : SkutellaCQP.MaxCut.eq_37
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:12:07.331137+00:00
-- url     : https://prove2.me/theorems/e21d1e1b-e3dd-4c8c-856b-ff53486bbfdf
-- title:
--   (37), p. 31 — Z* ≥ Z*_CQP = 1/m · c(E_J) + (1/2 + 1/(2m)) Σⱼ wⱼpⱼ
-- statement:
--   Consider $n$ jobs with processing times $p_j>0$ and weights $w_j\ge0$ on $m\ge1$ identical parallel machines, the graph $G_J$ of total weight $c(E_J)$, and the vector $\bar a_{ij}=1/m$ of Lemma 2.5. Then the optimum value $Z^*_{CQP}=Z_{CQP}(\bar a)$ of the relaxation (CQP) satisfies
--   $$
--   Z_{CQP}(\bar a)=\frac1m\,c(E_J)+\Big(\frac12+\frac1{2m}\Big)\sum_j w_jp_j ,
--   $$
--   and it is a lower bound on the value of every schedule: $Z_{CQP}(\bar a)\le\sum_j w_jC_j(\sigma)$ for every assignment $\sigma$ of the jobs to the machines, so $Z^*\ge Z^*_{CQP}$.
--
--   Combined with (36), this lower bound on the scheduling optimum becomes the upper bound (38) on the maximum $m$-cut.
--
--   **Formalization Note** $Z^*$ is the minimum of the value over assignments (Smith's rule, p. 7), so "$Z^*\ge Z^*_{CQP}$" is stated against every assignment.
-- source:
--   Skutella, Convex quadratic and semidefinite programming relaxations in scheduling, J. ACM 48 (2001), p. 31, §6, proof of Theorem 6.1, display (37)

import Mathlib
import Definitions.Def_SkutellaCQP_MaxCut_Setting

namespace SkutellaCQP.MaxCut

open Finset

/-- Display (37), §6, proof of Theorem 6.1, p. 31. The optimum value of (CQP),
attained at `ā ≡ 1/m` (Lemma 2.5), equals `1/m · c(E_J) + (1/2 + 1/(2m)) ∑_j w_j p_j`, and it is a
lower bound on the value `∑_j w_j C_j` of every schedule (`Z* ≥ Z*_CQP`). -/
theorem eq_37 {m n : ℕ} (p w : Fin n → ℝ) (hp : ∀ j, 0 < p j) (hw : ∀ j, 0 ≤ w j) (hm : 0 < m) :
    ZCQP p w (abar m n) =
        1 / (m : ℝ) * cE p w + (1 / 2 + 1 / (2 * (m : ℝ))) * ∑ j, w j * p j ∧
    ∀ τ : Fin n → Fin m, ZCQP p w (abar m n) ≤ val p w τ := by sorry

end SkutellaCQP.MaxCut
