-- Prove2me | Theorems.Thm_ResAllocGaps_example_3
-- name    : ResAllocGaps.example_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:31:30.637299+00:00
-- url     : https://prove2.me/theorems/c9a48019-6791-4883-b9db-91f75b51cbde
-- title:
--   Example 3 — $F_\beta$ of (1) is a $(\beta,1/2)$-clustered law on $[0,1]$
-- statement:
--   For every $\beta\ge0$ the law $F_\beta$ of display (1) (density $f_\beta$) satisfies:
--
--   1. it is a probability measure with $F_\beta([0,1])=1$;
--   2. its distribution function on $[0,1]$ is the $F_\beta(x)$ of (1);
--   3. its generalized inverse is
--   $$F_\beta^{-1}(q)=\frac{1-(1-2q)^{1/(\beta+1)}}{4}\ \ (0<q\le\tfrac12),\qquad F_\beta^{-1}(q)=\frac{(2q-1)^{1/(\beta+1)}+3}{4}\ \ (\tfrac12<q\le1);$$
--   4. the gap $(\tfrac14,\tfrac34)$ has mass $0$ and the clusters $[0,\tfrac14]$, $[\tfrac34,1]$ have mass $\tfrac12$ each;
--   5. $F_\beta$ is $(\beta,\tfrac12)$-clustered, i.e. belongs to $\mathscr F_{\beta,1/2}$.
--
--   This places the hard instance of the lower bound in the class of the goal theorem, for every $\beta\ge0$.
--
--   **Formalization Note** The law is defined by its density; its distribution function is a conclusion.
--
--   Differences from the source:
--   - reading: F_β⁻¹(q) = [1/4, 3/4] at q = 1/2 (set-valued) → F_β⁻¹(1/2) = 1/4, the first branch on (0, 1/2]; reason: p.11 defines F⁻¹(q) = inf{v : F(v) ≥ q}, which is 1/4 at q = 1/2
--   - reading: first branch of F_β⁻¹ for 0 ≤ q ≤ 1/2 → first branch for 0 < q ≤ 1/2; reason: at q = 0 the p.11 definition gives inf ℝ = −∞, not the printed 0; Definition 1 evaluates F⁻¹ only on (0, 1]
--   - encoding: F_β given by its distribution function (1); one gap G₁ = (1/4, 3/4) and clusters H₁ = [0, 1/4], H₂ = [3/4, 1] → muBeta β defined by the density f_β = F_β′, with the cdf identity, the gap mass 0 and the cluster masses 1/2 as clauses; reason: same law; the gap and cluster statements are the p.11 meaning of 'gap' and 'cluster'
-- source:
--   O. Besbes, Y. Kanoria and A. Kumar, Dynamic Resource Allocation: Algorithmic Design Principles and Spectrum of Achievable Performances, arXiv:2205.09078v2 (6 Oct 2023), https://arxiv.org/abs/2205.09078v2, §3.1, p.13, Example 3 and display (1); restated as (EC.1), p.ec1

import Mathlib
import Definitions.Def_ResAllocGaps_quantile
import Definitions.Def_ResAllocGaps_IsClustered
import Definitions.Def_ResAllocGaps_muBeta

open MeasureTheory ProbabilityTheory

namespace ResAllocGaps

/-- **Example 3**, display (1), Besbes, Kanoria & Kumar, arXiv:2205.09078v2, p.13 (restated as
(EC.1) on p.ec1 with `g = 1/2`): for every `β ≥ 0` the law `F_β` of (1) is a probability measure on
`[0, 1]` whose distribution function is (1), whose quantile function is the `F_β⁻¹` of (1), with
one gap `G₁ = (1/4, 3/4)` and clusters `H₁ = [0, 1/4]`, `H₂ = [3/4, 1]` of mass `1/2` each, and
"It is easy to see that `F_β⁻¹` in (1) is a `(β, 1/2)`-clustered distribution".

**Formalization Note.** `muBeta β` is defined by its density; the identification of its `cdf`
with (1) on `[0, 1]` is a clause here. At `q = 1/2` the page prints the interval `[1/4, 3/4]`; the
paper's own definition `F⁻¹(q) = inf {v : F(v) ≥ q}` (p.11) gives `1/4`, which is the value of
the first branch of (1) at `q = 1/2`, so the first branch is stated on `(0, 1/2]`. -/
theorem example_3 (β : ℝ) (hβ : 0 ≤ β) :
    IsProbabilityMeasure (muBeta β) ∧ muBeta β (Set.Icc 0 1) = 1 ∧
      (∀ x ∈ Set.Icc (0 : ℝ) 1, cdf (muBeta β) x = FbetaCdf β x) ∧
      (∀ q ∈ Set.Ioc (0 : ℝ) (1 / 2),
        quantile (muBeta β) q = (1 - (1 - 2 * q) ^ (1 / (β + 1))) / 4) ∧
      (∀ q ∈ Set.Ioc (1 / 2 : ℝ) 1,
        quantile (muBeta β) q = ((2 * q - 1) ^ (1 / (β + 1)) + 3) / 4) ∧
      muBeta β (Set.Ioo (1 / 4) (3 / 4)) = 0 ∧
      muBeta β (Set.Icc 0 (1 / 4)) = 1 / 2 ∧ muBeta β (Set.Icc (3 / 4) 1) = 1 / 2 ∧
      IsClustered (muBeta β) β (1 / 2) 0 := by sorry

end ResAllocGaps
