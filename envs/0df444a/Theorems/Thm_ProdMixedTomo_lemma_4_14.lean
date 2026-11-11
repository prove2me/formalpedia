-- Prove2me | Theorems.Thm_ProdMixedTomo_lemma_4_14
-- name    : ProdMixedTomo.lemma_4_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:20:43.072694+00:00
-- url     : https://prove2.me/theorems/12020865-ec1c-4111-b239-a7cbf4dc18ca
-- title:
--   Lemma 4.14 — key geometric lemma (corrected: $\epsilon\le\epsilon_0$)
-- statement:
--   For every goodness constant $K$ there are constants $C,\epsilon_0>0$ such that the following holds. Let $\mathrm{Bern}(\mu)$ have mean $\mu\in[0,1]^n$, let $0<\epsilon\le\epsilon_0$, and let $S=S_g\cup S_b\setminus S_r$ be a list of $N\ge1$ points where $S_g$ is $(K,\epsilon)$-good for $\mathrm{Bern}(\mu)$, $S_r\subseteq S_g$ and $|S_b|=|S_r|\le\epsilon N$. Then for every $w\in\mathcal W_{N,\epsilon}$,
--   $$
--   \|\mu(w)-\mu\|_{\mu(w)}\ \le\ C\Bigl(\sqrt{\epsilon\cdot\sup_{y\in T_{\mu(w)}}y^\top\Pi_{\mathrm{off}}(\Sigma(w))\,y}+\epsilon L(1/\epsilon)\Bigr).
--   $$
--   Deviation of the weighted mean in the test norm is thus certified by the off-diagonal second moment, which is what the filter drives down.
--
--   **Formalization Note** $S$ is aligned with $S_g$: it differs from $S_g$ in at most $\epsilon N$ positions (the removed $S_r$ and inserted $S_b$); $\mu(w)$ and $\Sigma(w)$ are computed from $S$.
--
--   Differences from the source:
--   - correction: no smallness condition on ϵ → ∃ ϵ₀ > 0 (with C, for each K) and ϵ ≤ ϵ₀; reason: the printed lemma is false at ϵ = 0.4: take μ = (½,…,½), S = S_g a good set whose first point x₁ has ≥ n/4 zero coordinates, w = e₁/N ∈ 𝒲_{N,0.4}; then μ(w) = x₁, Σ(w) = 0, the right side is 0.4·C, while y = −𝟙{x₁ᵢ = 0} ∈ T_{x₁} gives ‖μ(w) − μ‖_{μ(w)} ≥ n/8; the proof uses "for sufficiently small ϵ" (p.28) and Theorem 4.5 already assumes ϵ ≤ ϵ₀
--   - reading: "S_g is an ϵ-good set" (≲ inside Definition 4.11) and ≲ in the conclusion → ∀ K ∃ C, ϵ₀ with (K, ϵ)-goodness; reason: reading R8
--   - encoding: the multiset S = S_g ∪ S_b \ S_r with |S_b| = |S_r| ≤ ϵN → lists S, S_g of length N differing in at most ϵN positions; reason: goodness and 𝒲_{N,ϵ} are permutation invariant, so the points can be ordered so that S_b replaces S_r position by position
--   - encoding: N samples (implicit N ≥ 1) → hypothesis 0 < N; reason: excludes only the empty sample, where μ(w) is undefined (w = 0 ∉ Γ_N \ {0})
--   - reading: log(1/t) in an upper bound → max{1, log(1/t)} (logPlus), natural log; reason: the paper's convention, §2 Notation p.13
-- source:
--   Arulandu, Diakonikolas, Kane, Li, Agnostic Product Mixed State Tomography via Robust Statistics, arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), Lemma 4.14, p.27 (PDF p.29); proof pp.27–28

import Mathlib
import Definitions.Def_ProdMixedTomo_Rates
import Definitions.Def_ProdMixedTomo_BinaryProduct
import Definitions.Def_ProdMixedTomo_TestNorms
import Definitions.Def_ProdMixedTomo_Weights
import Definitions.Def_ProdMixedTomo_Goodness

namespace ProdMixedTomo

/-- Arulandu, Diakonikolas, Kane, Li, *Agnostic Product Mixed State Tomography via Robust Statistics*, arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), Lemma 4.14, p.27 (PDF p.29), **corrected**: with `ϵ ≤ ϵ₀`. Let `π` be a binary product
distribution with mean `μ ∈ [0,1]ⁿ`. Let `S = S_g ∪ S_b \ S_r` where `S_g` is an `ϵ`-good set of
points for `π`, `S_r ⊆ S_g` and `|S_b| = |S_r| ≤ ϵN`. Let `w ∈ 𝒲_{N,ϵ}`. Then
`‖μ(w) − μ‖_{μ(w)} ≲ √(ϵ · sup_{y ∈ T_{μ(w)}} yᵀ Π_off(Σ(w)) y) + ϵ log 1/ϵ`.

**Formalization Note.** Correction: the printed lemma has no smallness condition on `ϵ`, and it
is false at `ϵ = 0.4` (a weight on a single sample point, see the mission notes); the proof uses
"for sufficiently small ϵ". The lemma is stated for `ϵ ≤ ϵ₀` with `ϵ₀` chosen with the constant.
For every goodness constant `K` there are `C, ϵ₀`. The corrupted list `S` is aligned with `S_g`:
it differs from `S_g` in at most `ϵN` positions (the removed `S_r` and the inserted `S_b`).
`N > 0` (a sample set; `μ(w)` needs `w ≠ 0`). -/
theorem lemma_4_14 :
    ∀ K : ℝ, ∃ C ϵ₀ : ℝ, 0 < C ∧ 0 < ϵ₀ ∧
    ∀ (n N : ℕ) (ϵ : ℝ) (μ : Fin n → ℝ) (Sg S : Fin N → Cube n) (w : Fin N → ℝ),
      0 < N → 0 < ϵ → ϵ ≤ ϵ₀ → μ ∈ MeanBox n → IsGood K ϵ μ (pts Sg) →
      ((Finset.univ.filter fun i => S i ≠ Sg i).card : ℝ) ≤ ϵ * N →
      w ∈ Wset N ϵ →
      vnorm (wMean (pts S) w) (wMean (pts S) w - μ) ≤
        C * (Real.sqrt (ϵ * sSup ((fun y => y ⬝ᵥ (offDiag (wCov (pts S) w)).mulVec y) ''
            Tset (wMean (pts S) w))) + ϵ * logPlus (1 / ϵ)) := by sorry

end ProdMixedTomo
