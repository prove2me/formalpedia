-- Prove2me | Theorems.Thm_SubquadCutReach_Faster_Supplement_lemma_3_7
-- name    : SubquadCutReach.Faster.Supplement.lemma_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:24:18.423989+00:00
-- url     : https://prove2.me/theorems/8cb89366-5525-4128-8d7c-a61b38a4e865
-- title:
--   Lemma 3.7 — Simple averaging (Algorithm 1)
-- statement:
--   Let $H$ be a simple graph on $n$ labelled vertices, accessible only through undirected cut queries $S\mapsto|E_H(S,V\setminus S)|$, and let $b^*\in\mathbb Z^n$ be a feasible target imbalance vector: some orientation of $H$ has imbalance $b^*$. Let $z_1,\dots,z_T$ be the orientation rules of Algorithm 1 (step $\eta=1/(2n\sqrt{2T})$, $y_1=0$, pairs directed from the smaller to the larger $y_t$-value with ties from the smaller label, $y_{t+1}=y_t+\eta(b_{z_t}-b^*)$), and let $\bar z=\frac1T\sum_t z_t$.
--
--   There is a constant $C>0$ and one deterministic cut-query program such that, for every integer $1\le T\le n$, every such $H$ and every feasible $b^*$, the program, given $n$, $T$ and $b^*$, halts after at most $C\,nT$ cut queries with output exactly $z_1,\dots,z_T$, and
--
--   $$\|b_{\bar z}-b^*\|_1\le\frac{4n^2}{\sqrt T}.$$
--
--   This is the averaging step of the warm-up protocol: an average of integral orientations whose imbalance is close to the target, at a query cost linear in $nT$.
--
--   **Formalization Note** The program is a finite rational-literal oracle program of the mission's published model; it never sees $H$ or an orientation realising $b^*$. The query count is the charged count of the published model (each vertex-imbalance instruction costs six cut queries). The constant $C$ is chosen before $n$, $T$, $H$ and $b^*$.
--
--   Differences from the source:
--   - encoding: Algorithm 1 deterministically uses $O(nT)$ undirected cut queries → one `Admissible`, `Deterministic` program with `RunsWithin … (C*n*T)` and $C>0$ quantified before all instances; reason: the published operational cost model, with a uniform constant
--   - encoding: rules $z_1,\dots,z_T$ and potentials $y_1,\dots$ → 0-based `warmRule H b T t`, `warmPotential`, output read by `outputRules` and required to agree on every pair $u<v$; reason: index shift; rule cells with $u\ge v$ carry no direction in the published `directs`
--   - encoding: $b_{\bar z}$ by formula (3) → `fractionalImbalance H (warmAverage H b T)` with the $\pm1$ encoding of Definition 3.6; reason: the same formula
--   - reading: "Only the imbalance computation requires queries to H" → no separate clause; reason: a description of the algorithm, fixed by the output equality, with the cut oracle as the only access to $H$
-- source:
--   Henry Fleischmann, Sagnik Mukhopadhyay, Swagato Sanyal, STOC 2027 submission #503 (October 2026), p. 9, Lemma 3.7 and Algorithm 1 (PDF p. 11); restated p. 13 (PDF p. 15), proof pp. 14–15 (PDF pp. 16–17)

import Definitions.Def_SubquadCutReach_Faster_Tasks
import Definitions.Def_SubquadCutReach_Faster_Supplement_Warmup

set_option autoImplicit false

namespace SubquadCutReach.Faster.Supplement

open SubquadCutReach.Faster

/-- Lemma 3.7, p. 9 (PDF 11), restated p. 13 (PDF 15). One deterministic cut-query program,
uniform over all instances, outputs exactly the rules `z_1, …, z_T` of Algorithm 1 with at most
`C·n·T` charged queries; their average satisfies `‖b_z̄ - b*‖₁ ≤ 4n²/√T`. -/
theorem lemma_3_7 :
    ∃ C : ℝ, 0 < C ∧ ∃ P : Program, Admissible P ∧ Deterministic P ∧
      ∀ (n T : ℕ) (H : SimpleGraph (Fin n)) (b : Fin n → ℤ),
        1 ≤ T → T ≤ n → Feasible H b →
        RunsWithin P (cut H) (targetInput b T)
          (fun m => (∀ t : Fin T, ∀ u v : Fin n, u < v →
              outputRules n T m t u v = warmRule H b T t.val u v) ∧
            l1 (fun v => fractionalImbalance H (warmAverage H b T) v - (b v : ℝ)) ≤
              4 * (n : ℝ) ^ 2 / Real.sqrt (T : ℝ))
          (C * n * T) := by sorry

end SubquadCutReach.Faster.Supplement
