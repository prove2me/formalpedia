-- Prove2me | Theorems.Thm_SBMThreshold_Main_lemma_3_5
-- name    : SBMThreshold.Main.lemma_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:18:55.913657+00:00
-- url     : https://prove2.me/theorems/40443ed9-15d6-4d1a-8c42-d6e5bdf6fddc
-- title:
--   Lemma 3.5, p. 12 — E[Y | σ_U] = (1 + n^{−1+o(1)})(s^k/n) Σ σ_uσ_v and Var[Y | σ_U] = O(|U₁||U₂|(|U₁|+|U₂|) s^{2k}/n²)
-- statement:
--   Under the hypotheses of Theorem 2.8, for disjoint vertex sets $U_1,U_2$ put $U=U_1\cup U_2$, $Y=\sum_{u\in U_1,v\in U_2}Y_{u,v}$ and, for a labelling $\tau$, $S_\tau=\sum_{u\in U_1,v\in U_2}\tau_u\tau_v$. For every sequence $e_n\to0$ there are a sequence $c_n\to0$ and a constant $C$ such that, for all $n$, all disjoint $U_1,U_2$ with $|U_1|,|U_2|\le n^{e_n}$ and all labellings $\tau$:
--   1. $\displaystyle\Bigl|\mathbb E[Y\mid\sigma_U=\tau_U]-\frac{s^k}{n}S_\tau\Bigr|\le n^{-1+c_n}\frac{|s|^k}{n}|S_\tau|$;
--   2. $\displaystyle\operatorname{Var}[Y\mid\sigma_U=\tau_U]\le C\,|U_1||U_2|(|U_1|+|U_2|)\frac{s^{2k}}{n^2}$.
--
--   In display form the first claim is
--   $$
--   \mathbb E[Y\mid\sigma_U]=(1+n^{-1+o(1)})\frac{s^k}{n}\sum_{u\in U_1,v\in U_2}\sigma_u\sigma_v .
--   $$
--
--   The lemma aggregates the path sums between two small vertex sets; it is the estimate the algorithm uses to propagate a correlated labelling from a seed set.
--
--   **Formalization Note** $\operatorname{Var}[Y\mid\sigma_U]=\mathbb E[Y^2\mid\sigma_U]-\mathbb E[Y\mid\sigma_U]^2$. The factor $(1+n^{-1+o(1)})$ is unfolded as an error bound relative to $|S_\tau|$, which also covers $S_\tau=0$. The size antecedent and the uniformity are read as in Theorem 2.8 (1); $O(\cdot)$ is an explicit constant $C$ chosen before $n$, the sets and the labellings.
-- source:
--   Mossel, Neeman and Sly, A Proof of the Block Model Threshold Conjecture, arXiv:1311.4115v4, p. 12, Lemma 3.5 (under the assumptions of Theorem 2.8, p. 5)

import Mathlib
import Definitions.Def_SBMThreshold_Main_Setting
import Definitions.Def_SBMThreshold_Main_Paths
open Filter Topology Finset

namespace SBMThreshold.Main

/-- Lemma 3.5 (p. 12): for disjoint `U₁, U₂` of size at most `n^{o(1)}`, `U = U₁ ∪ U₂` and
`Y = Σ_{u ∈ U₁, v ∈ U₂} Y_{u,v}`, uniformly over labellings of `U`,
`E[Y | σ_U] = (1 + n^{-1+o(1)}) (s^k/n) Σ_{u ∈ U₁, v ∈ U₂} σ_u σ_v` and
`Var[Y | σ_U] = O(|U₁||U₂|(|U₁| + |U₂|) s^{2k}/n²)`. -/
theorem lemma_3_5 (a b : ℕ → ℝ) (ℓ : ℕ → ℕ) (lam α : ℝ)
    (hA : Assumption27 a b ℓ) (hP : Theorem28Params a b lam α) :
    ∀ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) →
      ∃ c : ℕ → ℝ, Tendsto c atTop (𝓝 0) ∧ ∃ C : ℝ,
        ∀ (n : ℕ) (U₁ U₂ : Finset (Fin n)) (τ : Fin n → Bool),
          Disjoint U₁ U₂ → (U₁.card : ℝ) ≤ (n : ℝ) ^ (e n) → (U₂.card : ℝ) ≤ (n : ℝ) ^ (e n) →
          |condExp n (a n) (b n) (U₁ ∪ U₂) τ (fun _ G =>
                ∑ u ∈ U₁, ∑ v ∈ U₂, pathY n (a n) (b n) (pathLen α n) u v G) -
              sPar (a n) (b n) ^ pathLen α n / n *
                ∑ u ∈ U₁, ∑ v ∈ U₂, spin (τ u) * spin (τ v)| ≤
            (n : ℝ) ^ (-1 + c n) * (|sPar (a n) (b n)| ^ pathLen α n / n) *
              |∑ u ∈ U₁, ∑ v ∈ U₂, spin (τ u) * spin (τ v)| ∧
          condExp n (a n) (b n) (U₁ ∪ U₂) τ (fun _ G =>
                (∑ u ∈ U₁, ∑ v ∈ U₂, pathY n (a n) (b n) (pathLen α n) u v G) ^ 2) -
              condExp n (a n) (b n) (U₁ ∪ U₂) τ (fun _ G =>
                ∑ u ∈ U₁, ∑ v ∈ U₂, pathY n (a n) (b n) (pathLen α n) u v G) ^ 2 ≤
            C * ((U₁.card : ℝ) * U₂.card * (U₁.card + U₂.card)) *
              (sPar (a n) (b n) ^ (2 * pathLen α n) / (n : ℝ) ^ 2) := by sorry

end SBMThreshold.Main
