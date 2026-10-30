-- Prove2me | Theorems.Thm_PigeonholeDesignAudit_Lower_lemma_4_all_finite_partitions
-- name    : PigeonholeDesignAudit.Lower.lemma_4_all_finite_partitions
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:41:11.895522+00:00
-- url     : https://prove2.me/theorems/2c4f797c-242a-4b94-87c5-5a3ce051af54
-- title:
--   Lemma 4 — every finite partition has worst-case expected discrepancy Ω(T^(1/4))
-- statement:
--   Consider one continuous covariate in $[0,1]$ and no discrete covariates. There are an absolute constant $c>0$ and a natural threshold $T_0\ge2$ such that, for every even $T\ge T_0$, every integer $K\ge1$, and every time-invariant label map $h:\mathbb R\to\operatorname{Fin}K$, there is an arrival sequence $x\in[0,1]^T$ for which
--   $$\frac{1}{2^T}\sum_{\omega\in\{0,1\}^T} d\bigl(x,W(h,x,\omega)\bigr)\ge cT^{1/4}.$$
--   Here $W$ is Definition 3: global capacity $T/2$ has priority, otherwise the subject joins the less populated group in its cell, using a fresh fair coin on a tie. For its final control and treatment groups $A,B$, the cost is $d(x,W)=\min_{e:A\simeq B}\sum_{a\in A}|x_a-x_{e(a)}|$. This is total cost with arbitrary cross-cell rematching. The hard sequence can depend on $T,K,h$, and is fixed before any assignment coins. The constant and threshold are independent of all three. Cells may be disconnected or nonmeasurable and $K$ may exceed $T$.
--
--   This is the full finite-partition content of Lemma 4. The existing Proved interval-partition theorem does not cover this domain. No supporting lower bound, geometric regularity or conditional independence claim is a hypothesis.
--
--   Differences from the source:
--   - encoding: finite time-invariant partitions of [0,1] → arbitrary hole : ℝ → Fin K for every K≥1, allowing unused labels; reason: fibers on [0,1] encode every finite partition; unused labels and arbitrary extension outside [0,1] never affect a run.
--   - reading: partition disjointness printed for all k,k′ → distinct fibers are disjoint; no self-disjointness requirement; reason: the literal self-disjoint reading forces empty cells and cannot cover [0,1]; the word partition and unique-cell rule require distinct indices.
--   - encoding: subjects 1,…,T and control/treatment assignments → Fin T indices and Boolean assignments with false control and true treatment; reason: bijection of subject indices preserves repeated covariates as distinct subjects and all matching costs.
--   - encoding: expected minimum total matching cost under fresh fair tie coins → phdExp averages the real infimum over bijections over all 2^T Boolean coin vectors; reason: the referenced balance theorem gives equal finite groups and an attained finite minimum; independent uniform bits implement exactly Definition 3 with the capacity check first.
--   - encoding: uniform worst-case Ω(T^(1/4)) on even horizons → ∃ c>0, ∃ T₀≥2, ∀ even T≥T₀, ∀ K≥1, ∀ hole, ∃ x∈[0,1]^T, c*T^(1/4)≤phdExp hole x; reason: makes the absolute asymptotic constant, finite initial exclusion and oblivious adversary explicit without restricting any large even horizon or partition.
-- source:
--   Zhao and Zhou, Pigeonhole Design: Balancing Sequential Experiments from an Online Matching Perspective, arXiv:2201.12936v6, 23 May 2024, https://arxiv.org/abs/2201.12936v6, Lemma 4, printed/PDF p. 18; model printed/PDF pp. 9–12; Definition 3 printed/PDF p. 16; proof §EC.7 printed pp. ec15–ec16 / PDF pp. 53–54; PDF SHA-256 14ac232ec751818d9529cdaccb8d255b4003e9ccdbdeec925dcdbba4f7ca0cbb

import Mathlib
import Definitions.Def_PigeonholeDesign_Upper_Setting

namespace PigeonholeDesignAudit.Lower

/-- Zhao–Zhou, arXiv:2201.12936v6, Lemma 4, printed/PDF p. 18;
model pp. 9–12, Definition 3 p. 16, proof ec15–ec16 / PDF pp. 53–54.
The positive constant and threshold are uniform over horizons and all finite partitions.
Fibers of `hole` on `[0,1]` may be arbitrary sets, including disconnected or nonmeasurable
sets; unused labels and values outside `[0,1]` have no effect on a run. The partition is
fixed before the oblivious arrival sequence, which is fixed before fair assignment coins.
`phdExp` retains the global capacity override and averages the minimum total matching cost.
No interval hypothesis or proof-step lower bound is assumed. -/
theorem lemma_4_all_finite_partitions :
    ∃ c : ℝ, 0 < c ∧ ∃ T₀ : ℕ, 2 ≤ T₀ ∧
      ∀ T : ℕ, T₀ ≤ T → Even T →
        ∀ K : ℕ, 1 ≤ K → ∀ hole : ℝ → Fin K,
          ∃ x : Fin T → ℝ, (∀ t, x t ∈ Set.Icc (0 : ℝ) 1) ∧
            c * (T : ℝ) ^ ((1 : ℝ) / 4) ≤ PigeonholeDesign.Upper.phdExp hole x := by sorry

end PigeonholeDesignAudit.Lower
