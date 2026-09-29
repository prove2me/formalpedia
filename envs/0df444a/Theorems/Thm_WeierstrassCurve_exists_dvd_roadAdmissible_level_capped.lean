-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_dvd_roadAdmissible_level_capped
-- name    : WeierstrassCurve.exists_dvd_roadAdmissible_level_capped
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/1072283b-04c6-53d5-9838-1b1809404404
-- title:
--   Capped admissible auxiliary level dividing a given modulus
-- statement:
--   Let $e$ and $p$ be natural numbers, $W$ a Weierstrass curve over $\mathbb{Z}$, and $S$ a finite set of natural numbers such that every element of $S$ is prime, $p \in S$, and every prime $q$ with $q \mid \Delta_W$ in $\mathbb{Z}$ lies in $S$. Let $M$ be a nonzero natural number whose prime divisors all lie in $S$, such that $q^{e+1} \nmid M$ for every $q \in S$ with $q \ne p$, such that $p^2 \nmid M$ whenever either $p \mid \Delta_W$ or $p \nmid a_p(W)$, and such that $p \nmid M$ whenever both $p \nmid \Delta_W$ and $p \mid a_p(W)$; here $p \nmid \Delta_W$ is the condition `IsGoodPrimeFor` and $a_p(W)$ is `apOfModel`, namely $\#\mathrm{ZMod}\,p + 1$ minus the number of points of the reduction of $W$ modulo $p$. Then there exists a natural number $N$ with $M \mid N$ and $N \ne 0$ such that: every element of $S$ is prime, $p \in S$, every prime dividing $\Delta_W$ lies in $S$ (these three conjuncts repeat the hypotheses), every prime divisor of $N$ lies in $S$, and for every $q \in S$ with $q \ne p$ one has $q^e \mid N$ and $q^{e+1} \nmid N$; moreover, if $p \mid \Delta_W$ or $p \nmid a_p(W)$ then $p \mid N$ and $p^2 \nmid N$, while if $p \nmid \Delta_W$ and $p \mid a_p(W)$ then $p \nmid N$.
--
--   This is the elementary level-bookkeeping step in the choice of an auxiliary level for the curve $W$: it enlarges a given modulus $M$ to a level $N$ whose valuation at each prime of $S$ away from $p$ is exactly $e$, while preserving the prescribed behaviour at $p$ (exactly one factor of $p$ in the ordinary or bad case, none in the good case with $p \mid a_p$). It is used by [`WeierstrassCurve.exists_heckeGaloisRepDatum_of_isResiduallyModularOfLevel_capped`](thm.html#WeierstrassCurve.exists_heckeGaloisRepDatum_of_isResiduallyModularOfLevel_capped).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_dvd_roadAdmissible_level_capped.lean

import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.exists_dvd_roadAdmissible_level_capped (e : ℕ) (p : ℕ) (W : WeierstrassCurve ℤ)
    (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) (hpS : p ∈ S)
    (hbadS : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ W.Δ → q ∈ S)
    (M : ℕ) (hM : NeZero M) (hMS : ∀ q : ℕ, q.Prime → q ∣ M → q ∈ S)
    (hMe : ∀ q ∈ S, q ≠ p → ¬ q ^ (e + 1) ∣ M)
    (hMp_ord : (¬ W.IsGoodPrimeFor p ∨ ¬ (p : ℤ) ∣ W.apOfModel p) → ¬ p ^ 2 ∣ M)
    (hMp_flat : W.IsGoodPrimeFor p → (p : ℤ) ∣ W.apOfModel p → ¬ p ∣ M) :
    ∃ N : ℕ, M ∣ N ∧ N ≠ 0 ∧
      (∀ q ∈ S, q.Prime) ∧ p ∈ S ∧
      (∀ q : ℕ, q.Prime → (q : ℤ) ∣ W.Δ → q ∈ S) ∧
      (∀ q : ℕ, q.Prime → q ∣ N → q ∈ S) ∧
      (∀ q ∈ S, q ≠ p → q ^ e ∣ N) ∧
      (∀ q ∈ S, q ≠ p → ¬ q ^ (e + 1) ∣ N) ∧
      ((¬ W.IsGoodPrimeFor p ∨ ¬ (p : ℤ) ∣ W.apOfModel p) → p ∣ N ∧ ¬ p ^ 2 ∣ N) ∧
      (W.IsGoodPrimeFor p → (p : ℤ) ∣ W.apOfModel p → ¬ p ∣ N) := by sorry
