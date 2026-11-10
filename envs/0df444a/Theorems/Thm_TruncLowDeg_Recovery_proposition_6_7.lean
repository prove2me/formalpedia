-- Prove2me | Theorems.Thm_TruncLowDeg_Recovery_proposition_6_7
-- name    : TruncLowDeg.Recovery.proposition_6_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:25:36.373903+00:00
-- url     : https://prove2.me/theorems/b77ac037-b9aa-45e2-8463-479b387edfef
-- title:
--   Proposition 6.7 — correctness of Algorithm 1: on the good event (probability $\ge1-\delta$) every output has $\hat\Sigma_0\succ0$ and $d_{TV}\le\varepsilon$
-- statement:
--   In the setting of Theorem 6.1, assuming that the preconditioning works as in Lemma 6.2 and (15) holds (which happens with probability at least $1-\delta$), Algorithm 1 outputs estimates $\hat\mu_0\in\mathbb R^d$ and $\hat\Sigma_0\succ0$ such that
--   $$d_{TV}\big(\mathcal N(\mu_0,\Sigma_0),\mathcal N(\hat\mu_0,\hat\Sigma_0)\big)\le\varepsilon .$$
--   Formally, with the implicit constants chosen sufficiently large in the order of the proof (batch and $\rho$-constants, then the constants of (14), then the $\eta$-constant), there are $C_4>0$ and a sample constant $C>0$ such that for every instance of Theorem 6.1 and every $n\ge(1/(\delta\varepsilon^2))(d/\alpha_0)^{Ck}$: (a) for every whitening rule of the preliminary batch (measurable in the samples), the good event "the preconditioning works, $|\hat{\mathcal D}|\ge|\hat{\mathcal D}_{rec}|/4$ and (15)" fails with probability at most $\delta$ over $n$ i.i.d. samples from $\mathcal N(\mu_0,\Sigma_0)|_{S_0}$; (b) on the good event Algorithm 1 has an output, and every output it can return, over all admissible choices in lines 9 and 11, is a pair $(\hat\mu_0,\hat\Sigma_0)$ with $\hat\Sigma_0\succ0$ and total variation distance at most $\varepsilon$. Together with Lemma 6.8 it gives Theorem 6.1.
--
--   Differences from the source:
--
--   - encoding: the implicit constants of Algorithm 1, of Lemma 5.4 and the (d/α₀)^{O(k)} in n → ∃ C₄ ∃ N₁ ∀ c_ρ ≥ N₁ ∃ N₂ ∀ c_q, c_r ≥ N₂ ∃ N₃ ∀ c with c_pre ≥ N₁ and c_η ≥ N₃ ∃ C > 0 (n ≥ (1/(δε²))(d/α₀)^{C·k}); reason: "sufficiently large" in the order the proof chooses them; the ladder lets Lemma 6.8's constants be met as well
--   - reading: a preliminary batch "of the size required by Lemma 5.4 with failure probability δ/2" (Õ(d³/α₀¹⁰ · log²(2/δ))) → `nPre = ⌈c_pre · d⁴/(α₀¹¹ δ)⌉` with the batch constant c_pre sufficiently large; reason: it dominates Lemma 5.4's requirement for large c_pre (polylog(d/α₀) ≤ O(d/α₀), log²(2/δ) = O(1/δ), as the paper notes on p. 28), is absorbed in the sample bound, and is computable with field operations and comparisons only (Lemma 6.8)
--   - generalization: line 4's T(x) = Σ̂_pre^{−1/2}(x − µ̂_pre) and line 14's Σ̂_pre^{1/2} → any whitening W of Σ̂_pre (W Σ̂_pre Wᵀ = I) in line 4 and W⁻¹ in line 14; the statement holds for every such W; reason: Σ̂_pre^{−1/2} is a whitening (then W⁻¹ = Σ̂_pre^{1/2}), so it specializes to the paper's algorithm; every whitening is QΣ̂_pre^{−1/2} with Q orthogonal, and the variant is what an exact implementation can compute (Lemma 6.8)
--   - encoding: "the preconditioning works as in Lemma 6.2 and (15) holds" → `Good`: Lemma 6.2's event, |𝒟̂| ≥ |𝒟̂_rec|/4, and (15); reason: (15) labels the display of Lemma 6.3, which contains the retention inequality; without it Algorithm 1 returns Fail at line 6
--   - encoding: "(which happens with probability at least 1 − δ)" → clause (a): the product measure of the samples outside the good event is at most δ; reason: failure-set form, avoiding an outer-measure reading
--   - encoding: Algorithm 1 outputs estimates with Σ̂₀ ≻ 0 and d_TV ≤ ε → clause (b): on the good event some output exists, and every output of the relation `Alg1Output` is `some (µ̂₀, Σ̂₀)` with Σ̂₀ positive definite and `tvDist` ≤ ε; reason: Algorithm 1 makes arbitrary admissible choices in lines 9 and 11, so the claim must hold for every one
--   - encoding: d_TV → `FoundationsRL.DECLower.tvDist`, the supremum over measurable sets of |P(A) − Q(A)|; reason: the definition of the total variation distance
--   - reading: empirical / sample covariance → normalization 1/m (`empCov`); reason: the paper does not fix the normalization; Lemma 5.4 holds for either
--   - encoding: ℝ^d, coordinates j ∈ {1, …, d} → `Vec d = EuclideanSpace ℝ (Fin d)`, 0-based coordinates `Fin d`; reason: Lean convention; same instances
-- source:
--   Vári-Kakas, Wiedmer, A General Approach to Polynomial-Time Truncated Learning via Low-Degree Moments, STOC 2027 submission (manuscript sha256 613f0e39…), p. 28, Proposition 6.7; proof pp. 28–29

import Definitions.Def_TruncLowDeg_Recovery_Algorithm
import Definitions.Def_FoundationsRL_DECLower_tvDist

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder

namespace TruncLowDeg.Recovery

/-- Proposition 6.7 (p. 28): correctness of Algorithm 1. With the implicit constants chosen
sufficiently large in the order of the proof (the batch and `ρ` constants first, then the two
constants of (14), then the `η` constant), there are a constant `C₄` (Lemma 5.4) and a sample
constant `C` such that, in the setting of Theorem 6.1 with `n ≥ (1/(δε²)) (d/α₀)^{Ck}` samples:
(a) for every whitening rule `W` of the preliminary batch (measurable as a function of the
samples, and a whitening of `Σ̂_pre` whenever `Σ̂_pre ≻ 0`), the event "the preconditioning works
as in Lemma 6.2, `|𝒟̂| ≥ |𝒟̂_rec|/4` and (15) holds" fails with probability at most `δ`;
(b) on this event Algorithm 1 has an output, and every output it can return (over all admissible
choices) is a pair `(µ̂₀, Σ̂₀)` with `Σ̂₀ ≻ 0` and `d_TV(N(µ₀, Σ₀), N(µ̂₀, Σ̂₀)) ≤ ε`.
The paper's algorithm is the whitening `W = Σ̂_pre^{−1/2}`. -/
theorem proposition_6_7 :
    ∃ C₄ : ℝ, 0 < C₄ ∧ ∃ N₁ : ℕ, ∀ cρ : ℕ, N₁ ≤ cρ → ∃ N₂ : ℕ, ∀ cq cr : ℕ, N₂ ≤ cq →
      N₂ ≤ cr → ∃ N₃ : ℕ, ∀ c : Consts, N₁ ≤ c.pre → c.rho = cρ → c.q = cq → c.r = cr →
      N₃ ≤ c.eta → ∃ C : ℝ, 0 < C ∧
      ∀ (d k : ℕ) (α₀ ε δ : ℝ) (μ₀ : Vec d) (Sig₀ : Mat d) (S₀ : Set (Vec d)),
      1 ≤ d → 1 ≤ k → 0 < α₀ → α₀ ≤ 1 → Sig₀.PosDef → BVD S₀ ≤ (k : ℕ∞) →
      ENNReal.ofReal α₀ ≤ gaussian μ₀ Sig₀ S₀ → 0 < ε → ε < 1 → 0 < δ → δ < 1 →
      ∀ n : ℕ, 1 / (δ * ε ^ 2) * ((d : ℝ) / α₀) ^ (C * k) ≤ n →
        (∀ Wb : List (Vec d) → Mat d,
          (∀ L : List (Vec d), (empCov L).PosDef → IsWhitening (empCov L) (Wb L)) →
          (∀ i j : Fin d,
            Measurable (fun X : Fin n → Vec d => Wb (batch c α₀ δ (List.ofFn X)) i j)) →
          (Measure.pi fun _ : Fin n => truncGaussian μ₀ Sig₀ S₀)
              {X | ¬ Good c C₄ d k α₀ ε δ μ₀ Sig₀ S₀ (List.ofFn X)
                (Wb (batch c α₀ δ (List.ofFn X)))} ≤ ENNReal.ofReal δ) ∧
        ∀ (X : Fin n → Vec d) (W : Mat d),
          Good c C₄ d k α₀ ε δ μ₀ Sig₀ S₀ (List.ofFn X) W →
          (∃ out, Alg1Output c d k α₀ ε δ (List.ofFn X) W out) ∧
          ∀ out, Alg1Output c d k α₀ ε δ (List.ofFn X) W out →
            ∃ (μh : Vec d) (Sh : Mat d), out = some (μh, Sh) ∧ Sh.PosDef ∧
              FoundationsRL.DECLower.tvDist (gaussian μ₀ Sig₀) (gaussian μh Sh) ≤ ε := by sorry

end TruncLowDeg.Recovery
