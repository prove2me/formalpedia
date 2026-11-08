-- Prove2me | Theorems.Thm_ProperHalfspace_proposition_12
-- name    : ProperHalfspace.proposition_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:03:44.053875+00:00
-- url     : https://prove2.me/theorems/6bface12-36a1-46e0-aeab-b052640c2a73
-- title:
--   Proposition 12 — basic properties of $M_\rho(f)$
-- statement:
--   For every $f:\{\pm1\}^n\to[-1,1]$ and $\rho\in[0,1]$:
--
--   1. $M_\rho(f)$ is positive semidefinite.
--   2. $\mathrm{Tr}(M_\rho(f))\le1$.
--   3. For every $i$,
--   $$M_\rho(f)_{ii}=(1-\rho)\sum_{A\subseteq[n]\setminus\{i\}}\rho^{|A|}\hat f(A\cup\{i\})^2=(1-\rho)\mathrm{Inf}^{(\rho)}_i[f],$$
--   and for distinct $i,j$,
--   $$M_\rho(f)_{ij}=(1-\rho)^2\sum_{A\subseteq[n]\setminus\{i,j\}}\rho^{|A|}\hat f(A\cup\{i\})\hat f(A\cup\{j\}).$$
--   4. For $\rho\in(0,1)$, $M_\rho(f)_{ii}=\frac{1-\rho}\rho\mathrm{Inf}_i[T_{\sqrt\rho}f]$.
--
--   The diagonal identity explains the name: up to scaling, the diagonal entries are the influences of the smoothed function.
--
--   Differences from the source:
--   - reading: the proposition's three items, with clause 4 as a display right after it → all four clauses in one statement; reason: p.21 cites clause 4 as "By Proposition 12"
-- source:
--   De, Mossel, Nadimpalli, Neeman, Efficient Proper Agnostic Learning of Halfspaces, arXiv:2611.02344 (Nov. 1, 2026), Proposition 12 and the display after it, p.18

import Mathlib
import Definitions.Def_ProperHalfspace_Fourier
import Definitions.Def_ProperHalfspace_InfluencePCA

namespace ProperHalfspace

/-- Proposition 12, p.18 (basic properties of `M_ρ(f)`), with the display right after it, which p.21 cites as "By Proposition 12".
De, Mossel, Nadimpalli, Neeman, arXiv:2611.02344 (Nov. 1, 2026). For `f : {±1}ⁿ → [−1, 1]` and `ρ ∈ [0, 1]`: `M_ρ(f)` is positive
semidefinite; `Tr M_ρ(f) ≤ 1`; (2) `M_ρ(f)_ii = (1−ρ) Σ_{A ⊆ [n]∖{i}} ρ^{|A|} f̂(A ∪ {i})² = (1−ρ) Inf_i^{(ρ)}[f]`;
(3) `M_ρ(f)_ij = (1−ρ)² Σ_{A ⊆ [n]∖{i,j}} ρ^{|A|} f̂(A ∪ {i}) f̂(A ∪ {j})` for `i ≠ j`; and for `ρ ∈ (0, 1)`,
`M_ρ(f)_ii = ((1−ρ)/ρ) Inf_i[T_{√ρ} f]`. -/
theorem proposition_12 {n : ℕ} (f : Cube n → ℝ) (hf : IsBoundedOne f) (ρ : ℝ) (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) :
    (pcaMatrix ρ f).PosSemidef ∧
    (pcaMatrix ρ f).trace ≤ 1 ∧
    (∀ i, pcaMatrix ρ f i i =
        (1 - ρ) * ∑ A ∈ (Finset.univ.erase i).powerset, ρ ^ A.card * fourier f (insert i A) ^ 2) ∧
    (∀ i, pcaMatrix ρ f i i = (1 - ρ) * noisyInfluence ρ f i) ∧
    (∀ i j, i ≠ j → pcaMatrix ρ f i j =
        (1 - ρ) ^ 2 * ∑ A ∈ ((Finset.univ.erase i).erase j).powerset,
          ρ ^ A.card * (fourier f (insert i A) * fourier f (insert j A))) ∧
    (0 < ρ → ρ < 1 → ∀ i, pcaMatrix ρ f i i = (1 - ρ) / ρ * influence (smooth ρ f) i) := by sorry

end ProperHalfspace
