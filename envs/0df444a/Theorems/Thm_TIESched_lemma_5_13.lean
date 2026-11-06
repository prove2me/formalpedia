-- Prove2me | Theorems.Thm_TIESched_lemma_5_13
-- name    : TIESched.lemma_5_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:46:56.640962+00:00
-- url     : https://prove2.me/theorems/f63898a0-e423-43df-807e-3fd2ada25389
-- title:
--   Lemma 5.13 — smooth truthful families with vanishing interactions and $C\le\Gamma(\mathrm{OPT}+|S|\delta)$
-- statement:
--   Let $(x,u)$ be a feasible, truthful fractional mechanism family with approximation guarantee $\Gamma$. For every $\delta>0$ there is a feasible truthful family $(x^\delta,u^\delta)$ whose allocation rules and normalized utilities are smooth and satisfy
--   $$C\big(p,x^{S,\delta}(p)\big)\le\Gamma\big(\mathrm{OPT}(p)+|S|\delta\big)\tag{7}$$
--   for every finite job set $S$ and every nonnegative report $p$ on $S$. If $(x,u)$ is padding-invariant, the new family also satisfies $G^{J,\delta}_{ij}(p)=0$ whenever $|J|\ge m$, for every $i$, $j\in J$ and nonnegative $p$ on $J$.
--
--   Differences from the source:
--   - reading: allocation rules and normalized utilities are smooth → C^∞ on all of ℝ^{m×S}; reason: the right averages are defined and smooth at every report (p.34, App. A.3 (1)); the strongest reading, which specializes to smoothness on the orthant
--   - reading: padding-invariant (T_v defined with one chosen fresh label per job set) → invariance for every fresh label k ∉ S; reason: the proof of Lemma 5.7 (p.25) views a job k ∈ J as the padding job of S∖{k}, which needs invariance for that label; the family of Lemma 5.6 is relabeling-equivariant, so the choice is immaterial (p.24)
--   - encoding: rules x^S, π^S on ℝ^{m×S}_{≥0} with values in X(S) → total functions on ℝ^{m×S}, with feasibility a separate predicate on nonnegative reports; reason: a family on the orthant extends to such a total function, and the hypotheses read nonnegative reports only
-- source:
--   Wang, Xu, Zhang, Tight Analysis of Randomized Truthful Scheduling: An (m+1)/2 Lower Bound, arXiv:2611.05142 (artifact sha256 a89db2da…), Lemma 5.13, p.34

import Mathlib
import Definitions.Def_TIESched_PaddingInvariant
import Definitions.Def_TIESched_interaction

set_option autoImplicit false

namespace TIESched

/-- **Lemma 5.13 (Vanishing interactions without continuity)** (Wang, Xu, Zhang, arXiv:2611.05142,
Lemma 5.13, p.34). Let `(x, u)` be a truthful fractional mechanism family with approximation
guarantee `Γ`. For every `δ > 0` there is a feasible truthful family `(x^δ, u^δ)` whose allocation
rules and normalized utilities are smooth and satisfy (7),
`C(p, x^{S,δ}(p)) ≤ Γ(OPT(p) + |S|δ)`, for every finite job set `S` and every nonnegative report `p`
on `S`. If `(x, u)` is padding-invariant, the new family also satisfies `G^{J,δ}_ij(p) = 0` whenever
`|J| ≥ m`, for every `i ∈ [m]`, `j ∈ J` and nonnegative report `p` on `J`.

**Formalization Note.** Smooth means `C^∞` on all of `ℝ^{m×S}` (the allocation rule as a map
`ℝ^{m×S} → ℝ^{m×S}`, each normalized utility as a map to `ℝ`). The bound (7) holds for every `S`,
including `S = ∅` and reports with `OPT(p) = 0`. The witness need not be padding-invariant. -/
theorem lemma_5_13 (m : ℕ) [NeZero m] (hm : 2 ≤ m) (Γ : ℝ) (M : FracMech m)
    (hfeas : Feasible M.alloc) (htr : Truthful M) (happ : IsApprox M Γ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ Mδ : FracMech m, Feasible Mδ.alloc ∧ Truthful Mδ ∧
      (∀ S : Finset ℕ, ContDiff ℝ (⊤ : ℕ∞) (Mδ.alloc S) ∧
        ∀ i : Fin m, ContDiff ℝ (⊤ : ℕ∞) (fun p => normalizedUtility Mδ S p i)) ∧
      (∀ (S : Finset ℕ) (p : Fin m → S → ℝ), IsNonneg p →
        makespan p (Mδ.alloc S p) ≤ Γ * (OPT p + (S.card : ℝ) * δ)) ∧
      (PaddingInvariant M → ∀ J : Finset ℕ, m ≤ J.card → ∀ p : Fin m → J → ℝ, IsNonneg p →
        ∀ (i : Fin m) (j : J), interaction Mδ.alloc J p i j = 0) := by sorry

end TIESched
