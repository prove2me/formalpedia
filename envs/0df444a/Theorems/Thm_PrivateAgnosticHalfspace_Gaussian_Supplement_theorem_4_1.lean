-- Prove2me | Theorems.Thm_PrivateAgnosticHalfspace_Gaussian_Supplement_theorem_4_1
-- name    : PrivateAgnosticHalfspace.Gaussian.Supplement.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T03:09:08.768047+00:00
-- url     : https://prove2.me/theorems/fc382140-d298-4858-92f2-b5f13daff109
-- title:
--   Theorem 4.1 — private proper Gaussian semi-agnostic learning
-- statement:
--   There are universal constants $C,A>0$, a natural exponent $r$, universal public schedule constants and one finite program such that the following holds. Let $\alpha,\beta,\varepsilon,\delta\in(0,1)$ and let $P$ be any binary-labeled distribution on $\mathbb R^d$ with standard Gaussian marginal. Algorithm 4 has unconditional dataset-level $(\varepsilon,\delta)$ privacy and returns a genuine affine halfspace. With its public integer sample schedule $n$,
--   $$n\le A\left(\frac d{\alpha^2}+\frac d{\varepsilon\alpha}\right)\Lambda^r,\qquad d\ge16\log(n/\beta)\ \Longrightarrow\ \Pr\{\operatorname{err}_P(h)\le C\operatorname{OPT}+\alpha\}\ge1-\beta.$$
--   Here $\Lambda=1+\log(1/\alpha)+\log(1/\beta)+\log(1/\varepsilon)+\log(1/\delta)$. No bound on OPT, or knowledge of OPT, is supplied to the learner. The probability includes data, Laplace/Gaussian/sphere coins and validation selection. The program halts on every sample and tape, realizing the algorithm law with charged work at most $A n d(1+\log(1/\alpha))$; the schedule also has $d\le n$.
--
--   This companion trades a universal multiplier on OPT for sample size and runtime polynomial in dimension and inverse accuracy, while retaining coefficient one on the additive $\alpha$.
--
--   **Formalization Note** The paper writes soft-O/Theta and intermediate O(alpha),O(beta) bounds. The pp.13–16 proof supplies universal constants and a fixed logarithm power, not numeric constants. The formal schedule fixes $\rho=\alpha/(4A_{\rm err}C_\eta)$ throughout Algorithm 4, $C\ge\max(2A_{\rm err},1/\eta_{\max})$ with $\eta_{\max}=1/4$, concentration budgets $\beta/[16K(T+2)]$, and validation slack at most $\alpha/2$. Positive rounding and public prefix/discard rules make all calls defined. The large-OPT regime is covered because $C\operatorname{OPT}\ge1$ there; the small-OPT regime retains an invoked geometric-grid call. The dimension condition uses the literal total $n$ and requested $\beta$; privacy is not conditioned on Gaussian samples remaining unclipped.
--
--   Differences from the source:
--   - encoding: Euclidean examples with labels ±1, affine thresholds, and positive integer dimension → EuclideanSpace over Fin d with d ≥ 1, Borel measures, Bool labels decoded as ±1, sign(0)=+1; reason: coordinate and label encodings preserve all source instances; all real affine thresholds remain allowed
--   - reading: Theta/O iteration and sample schedules and intermediate O(alpha),O(beta) guarantees → uniform public schedules, internal rho=alpha/(4 Aerr Ceta), and concentration and validation budgets totaling at most beta; reason: the proof permits universal rescaling; this realizes the printed additive alpha and confidence 1-beta without an OPT premise
--   - reading: geometric grid and iteration counts without rounding or a large-parameter completion → positive ceilings, etaMax=1/4, fixed halfspaces for grid calls outside (0,1/2), and public equal-block prefixes with discarded excess; reason: completes the asymptotic pseudocode on the entire printed domain; every nontrivial OPT regime retains a valid small-eta call
--   - encoding: ramp gradient and sphere projection in Algorithm 3 and Claim 4.3 → closed-band tangent subgradient, projected independent Gaussian, normalized update and normalized-Gaussian sphere law with an axis fallback at zero; reason: the source uses the unnormalized ramp; breakpoints use its closed-band formula and zero Gaussian has probability zero; no step assumes a success event
--   - reading: arithmetic runtime with symmetric eigendecomposition on p.34 and inverse normal CDF and trigonometric operations in Algorithm 3 → the published sampling real RAM extended by unit-cost sin, cos, pi and normal quantile, and a symmetric spectral projection charged 1+d³; reason: these source operations require explicit semantics and costs; they are not silently expressible in the base scalar alphabet
--   - generalization: runtime poly(n); no explicit facts about the schedule → charged work at most A·n·d·(1+log(1/α)), plus the conclusions d ≤ n and that the η-grid reaches 1/4; reason: the runtime account on p.16 proves O(nd log(1/α)) and uses d ≤ n; since d ≤ n this bound implies poly(n), so the statement specializes to the printed theorem
-- source:
--   Giorgio Racca, Amartya Sanyal, Vikrant Singhal, Privacy for Free in Efficient Agnostic Halfspace Learning, STOC 2027 submission #1006 (October 2026), canonical held submission (not a proceedings-acceptance claim), p.11, Theorem 4.1; Algorithms 3–4 pp.12,34; analysis pp.13–16,35–36

import Definitions.Def_PrivateAgnosticHalfspace_Gaussian_Supplement_SemiAgnostic

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false

namespace PrivateAgnosticHalfspace.Gaussian.Supplement

/-- Theorem 4.1 (pp.11,15--16,34--36), with public internal normalization
rho = alpha/(4*Aerr*Ceta). Only the multiplicative OPT constant is relaxed. -/
theorem theorem_4_1 :
    ∃ (c : SemiConstants) (code : Code) (C A : ℝ) (r : ℕ),
      8 ≤ c.error ∧ 1 < c.gridStart ∧ 1 ≤ c.gridLength ∧ c.etaMax = 1 / 4 ∧
      0 < c.kappa ∧ c.kappa ≤ 1 / 4 ∧ 0 < c.step ∧ c.step ≤ 1 ∧
      0 < c.iterations ∧ 0 < c.blockSample ∧ 0 < c.validation ∧
      max (2 * c.error) (1 / c.etaMax) ≤ C ∧ 0 < A ∧
      ∀ d : ℕ, 1 ≤ d → ∀ α β ε δ : ℝ,
      0 < α → α < 1 → 0 < β → β < 1 →
      0 < ε → ε < 1 → 0 < δ → δ < 1 →
      let n := semiSize c d α β ε δ
      let budget := ⌊A * n * d * (1 + Real.log (1 / α))⌋₊
      d ≤ n ∧
      (n : ℝ) ≤ A * ((d : ℝ) / α ^ 2 + d / (ε * α)) * logs α β ε δ ^ r ∧
      (∃ k : Fin (semiK c α), c.etaMax ≤ semiEta c α k.val) ∧
      ∃ L : PrivateUniformGen.Characterization.Mechanism (Example d) (Halfspace d) n,
        Realizes (semiLaw c d α β ε δ) L ∧
        PrivateUniformGen.Characterization.IsDP L ε δ ∧
        (∀ S : Fin n → Example d,
          ImplementsHalfspace code (budget + 1) budget d
            (semiInput c d α β ε δ (List.ofFn S)) (L S : Measure (Halfspace d))) ∧
        ∀ P : Measure (Example d), IsProbabilityMeasure P → P.map Prod.fst = gaussian d →
          16 * Real.log (n / β) ≤ d →
          Accurate L classifier P (C * opt d P + α) β := by sorry

end PrivateAgnosticHalfspace.Gaussian.Supplement
