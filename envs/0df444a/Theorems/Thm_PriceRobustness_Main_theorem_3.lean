-- Prove2me | Theorems.Thm_PriceRobustness_Main_theorem_3
-- name    : PriceRobustness.Main.theorem_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T06:39:34.985502+00:00
-- url     : https://prove2.me/theorems/a495b3b8-5953-4789-b321-7ffc127d39e7
-- title:
--   Theorem 3(a)–(d): exact tail bound, equality, envelope and normal limit
-- statement:
--   The following four assertions are independently quantified.
--
--   (a) For any optimal robust decision, row $i$, maximizing protection pair and minimizing index as in Proposition 2, let $n=|J_i|$ and $1\le\Gamma_i\le n$. For any mutually independent measurable symmetric row noises taking values in $[-1,1]$, the source asserts
--   $$P\left\{\sum_{j\in J_i}\gamma_{ij}\eta_{ij}\ge\Gamma_i\right\}\le B(n,\Gamma_i).$$
--   The coefficients are exactly those constructed in Proposition 2; no bound on them is assumed.
--
--   (b) For every $1\le g\le n$ with $g$ integral and $g+n$ even, and every independent measurable family with $P(\eta_j=1)=P(\eta_j=-1)=1/2$, equality holds:
--   $$P\left\{\sum_{j=1}^n\eta_j\ge g\right\}=B(n,g).$$
--   This is the case of all coefficients equal to one, including $g=n$.
--
--   (c) For every $n$ and real $1\le\Gamma\le n$, with $\nu=(\Gamma+n)/2$, $k=\lfloor\nu\rfloor$ and $\mu=\nu-k$,
--   $$B(n,\Gamma)\le(1-\mu)C(n,k)+\sum_{l=k+1}^n C(n,l).$$
--   Here $B$ is the interpolated fair-binomial tail and $C$ is exactly the piecewise expression of Eq. (19), including $C(n,0)=C(n,n)=2^{-n}$.
--
--   (d) For every fixed real $\theta$,
--   $$\lim_{n\to\infty}B(n,\theta\sqrt n)=1-\Phi(\theta),$$
--   where $\Phi$ is the standard normal CDF. Clauses (c) and (d) are deterministic assertions and have no optimization or noise hypotheses. No restriction is imposed at the finitely many early indices of the limit.
--
--   The full source claim is preserved, including the recorded integer-budget defect in clause (a). The example with coefficients $(1,1,99,1)$ gives probability $1/2>B(4,2)=5/16$. This does not refute the different strict original-constraint bound or the normal limit.
--
--   Differences from the source:
--   - encoding: finite matrix indices and probability notation → Fin indices, an arbitrary measurable probability space, measurable real random variables and real-valued event probabilities; reason: finite relabeling and the standard measurable-probability convention preserve the source instances
--   - reading: the unbound j in the fractional term of Eq. (5) → the designated extra coordinate t; reason: the preceding model, the one-fractional-coordinate explanation and Eq. (9) fix that coordinate
--   - encoding: integer-budget endpoints on p. 6 and the pair notation of Proposition 2 → optional t and r, with S=J and no indices at full budget, including the empty row; reason: the outside branch is unused at full budget and no impossible extra index is required
--   - encoding: the quotient w_j/w_r with no convention when w_r=0 → real division assigns zero to a zero-denominator quotient; reason: this total-function extension retains otherwise undefined inputs and agrees with every defined quotient; no positivity hypothesis is added
--   - encoding: Model U defines eta=(a_tilde-a)/a_hat → realized entries are a+radius*eta on J, including zero radii; reason: the inverse representation agrees at positive radii and retains deterministic zero-radius entries without dividing by zero
--   - encoding: gamma_j=1 and an integral positive budget in clause (b) → a sum of the noises themselves and a natural budget g with 1≤g≤n and Even(g+n); reason: substitution removes only coefficients fixed to one; every admissible positive integer is represented
--   - encoding: the binomial sums and the standard normal integral → integer-threshold finite sums and the standard Gaussian measure of the lower half-line; reason: these give the identical binomial probabilities and normal CDF without a natural-floor truncation or an unspecified function
--   - generalization: positive square-root scaling in the eventual model budget regime → the same limit for every fixed real theta, with B defined at all real thresholds; reason: the displayed limit leaves theta unrestricted; the statement includes every positive theta in the eventual source regime, as well as zero and negative theta
-- source:
--   Bertsimas and Sim, The Price of Robustness, authors' preprint, August 2001; revised August, 2002; PDF SHA-256 63f0bffaff9128b706a084acc869e1020ce79adf86108ac23b5b0dd598f189cb; Theorem 3(a)–(d), pp. 10–11, Eqs. (16)–(20); proof pp. 29–33

import Definitions.Def_PriceRobustness_Main_RobustModel
import Definitions.Def_PriceRobustness_Main_Protection
import Definitions.Def_PriceRobustness_Main_Noise
import Definitions.Def_PriceRobustness_Main_Bounds

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
universe u

namespace PriceRobustness.Main

theorem theorem_3 :
    (∀ (m N : ℕ) (D : RobustModel m N) (x : Fin N → ℝ), D.Optimal x →
      ∀ (i : Fin m) (S : Finset (Fin N)) (t r : Option (Fin N)),
      MaximizesProtection (D.J i) (D.weight x i) (D.budget i) S t →
      MinimizesSelected (D.weight x i) S t r → 1 ≤ D.budget i →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (η : Fin N → Ω → ℝ), SymmetricNoise P (D.J i) η →
      P.real {ω | (∑ j ∈ D.J i, sourceGamma (D.weight x i) S r j * η j ω) ≥
        D.budget i} ≤ B (D.J i).card (D.budget i)) ∧
    (∀ (n g : ℕ), 1 ≤ g → g ≤ n → Even (g + n) →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (η : Fin n → Ω → ℝ),
      (∀ j, Measurable (η j)) → iIndepFun η P →
      (∀ j, P.real {ω | η j ω = 1} = 1 / 2 ∧
        P.real {ω | η j ω = -1} = 1 / 2) →
      P.real {ω | (∑ j, η j ω) ≥ (g : ℝ)} = B n g) ∧
    (∀ (n : ℕ) (Γ : ℝ), 1 ≤ Γ → Γ ≤ (n : ℝ) →
      B n Γ ≤ (1 - mu n Γ) * C n ⌊nu n Γ⌋ +
        ∑ l ∈ (Finset.range (n + 1)).filter (fun l : ℕ => ⌊nu n Γ⌋ + 1 ≤ (l : ℤ)),
          C n l) ∧
    (∀ θ : ℝ, Tendsto (fun n : ℕ => B n (θ * Real.sqrt n)) atTop
      (𝓝 (1 - Phi θ))) := by sorry

end PriceRobustness.Main
