-- Prove2me | Theorems.Thm_WiesemannRMDP_SRect_Supplement_theorem_5_5
-- name    : WiesemannRMDP.SRect.Supplement.theorem_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T10:57:54.699254+00:00
-- url     : https://prove2.me/theorems/6d1f1e2a-5856-49c9-a2e6-80e6415e95a1
-- title:
--   Theorem 5.5 — under (A1), (A2), (A3′) n^α d^H(Ξ_n, {ξ^0}) → 0 in probability for every α < 1/2
-- statement:
--   In the setting of Theorem 5.3, fix $\delta\ge0$ and let $(\xi^n)$ be any sequence of maximum likelihood estimators: almost surely, $\xi^n\in\Xi_0$ maximizes $\ell_n$ over $\Xi_0$. Let
--   $$\Xi_n:=\Xi_0\cap\{\xi\in\mathbb R^q:\phi_n(\xi)\ge0\},\qquad \phi_n(\xi):=[\nabla_\xi\ell_n(\xi^n)]^\top(\xi-\xi^n)-\tfrac12(\xi-\xi^n)^\top[\nabla^2_\xi\ell_n(\xi^n)](\xi-\xi^n)+\delta,$$
--   with the gradient and matrix given by the sums (37b) and (37c), and let $d^H(X,Y):=\max\{\sup_{x\in X}\inf_{y\in Y}\|x-y\|_\infty,\ \sup_{y\in Y}\inf_{x\in X}\|x-y\|_\infty\}$ be the Hausdorff distance. Under the assumptions (A1), (A2) and (A3′),
--   $$\operatorname{plim}_{n\to\infty}\Big(n^\alpha\, d^H\big[\Xi_n,\{\xi^0\}\big]\Big)=0\qquad\forall\,\alpha<1/2, \tag{38}$$
--   where plim denotes convergence in probability.
--
--   The theorem says the quadratic approximations $\Xi_n$ of the likelihood confidence regions shrink to the true parameter at any rate slower than $n^{-1/2}$; Proposition 5.6 and Corollary 5.8 build on it.
--
--   **Formalization Note** $d^H$ is Mathlib's extended Hausdorff distance on $\mathbb R^q$ with the sup norm, valued in $[0,\infty]$; an empty $\Xi_n$ is at distance $\infty$ from $\{\xi^0\}$, so no junk value $0$ enters. Convergence in probability is spelled out: for every $\varepsilon>0$ the outer probability of $\{n^\alpha d^H(\Xi_n,\{\xi^0\})\ge\varepsilon\}$ tends to $0$.
--
--   Differences from the source:
--
--   - generalization: (Ω, F, P) is the canonical space (S × A)^∞ with the product measure induced by π0 and P0 → any probability space with a process whose finite paths have the probabilities (32) at ξ0; reason: the conclusion depends only on the law of the observations, and the canonical space is one such space
--   - reading: ξn is "the" maximum likelihood estimator, which "may not be unique" (p. 31) → the theorem is stated for every sequence of almost-sure maximizers, measurable or not, and every fixed δ ≥ 0; reason: the paper fixes no selection and lets δ ∈ ℝ₊ be any constant (p. 32)
--   - encoding: d^H with values in [0, ∞) on the paper's sets → the extended Hausdorff distance in [0, ∞], with outer probabilities; reason: Ξn is bounded and contains ξn almost surely, where both agree; the outer measure removes the need for measurability of d^H(Ξn, {ξ0})
--   - encoding: the observation (s1, a1, …, sn, an) → X 0, …, X (n − 1); reason: Lean's time index starts at 0
--   - reading: "the MDP" of §5.1 satisfies definition (3) → the whole of Model.Standing is assumed; reason: r, λ do not occur in Theorem 5.5, so no instance is lost
-- source:
--   Wiesemann, Kuhn & Rustem, Robust Markov Decision Processes, Optimization Online 2610 (revision of February 9, 2012; sha256 8cbadb80…a79b), p. 35, Theorem 5.5 (38) and d^H; (36), (37a)–(37c) p. 34; δ p. 32; (A1) p. 29; (A2) p. 32; (A3') p. 34; proof Appendix C pp. 51–52

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_WiesemannRMDP_SRect_Model
import Definitions.Def_WiesemannRMDP_SRect_Supplement_Chains
import Definitions.Def_WiesemannRMDP_SRect_Supplement_Inference

open MeasureTheory ProbabilityTheory Filter FoundationsML.ReinforcementLearning Matrix
open scoped Topology ENNReal

namespace WiesemannRMDP.SRect.Supplement

open WiesemannRMDP.SRect

/-- Theorem 5.5 (Wiesemann, Kuhn & Rustem, *Robust Markov Decision Processes*, Optimization
Online 2610, revision of February 9, 2012, p. 35): under the assumptions (A1), (A2) and (A3'),
`plim_{n→∞} n^α d^H[Ξ_n, {ξ0}] = 0` for all `α < 1/2` (38).

`Ξ_n = Ξ0 ∩ {ϕ_n ≥ 0}` is the set (36), with `ϕ_n` the quadratic (37a) for a fixed `δ ≥ 0`,
centred at a maximum likelihood estimator `ξ_n`; the statement holds for every sequence of
maximum likelihood estimators. `d^H` is the Hausdorff distance for the `∞`-norm.

**Formalization Note.** `d^H` is `Metric.hausdorffEDist` on `Fin q → ℝ`, whose distance is the
sup norm; it takes values in `[0, ∞]` (an empty `Ξ_n` would be at distance `∞`, so no junk
value `0` enters). Convergence in probability is spelled out: for every `ε > 0` the outer
probability of `{n^α d^H(Ξ_n, {ξ0}) ≥ ε}` tends to `0`. -/
theorem theorem_5_5 {St Act : Type*} [Fintype St] [DecidableEq St] [Fintype Act]
    [DecidableEq Act] [Nonempty St] [Nonempty Act] {q L : ℕ} (M : Model St Act q L)
    (hM : M.Standing) (π0 : St → Act → ℝ) (hπ0 : IsPolicy π0)
    (ξ0 : Fin q → ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → St × Act) (hX : IsObservationProcess M π0 ξ0 P X)
    (hA1 : A1 M ξ0) (hA2 : A2 M π0) (hA3' : A3' M π0)
    (δ : ℝ) (hδ : 0 ≤ δ) (ξhat : ℕ → Ω → Fin q → ℝ) (hξhat : IsMLESeq M π0 X P ξhat) :
    ∀ α : ℝ, α < 1 / 2 → ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ => P {ω | ENNReal.ofReal ε ≤
        ENNReal.ofReal ((n : ℝ) ^ α) *
          Metric.hausdorffEDist (XiN M X δ n ω (ξhat n ω)) {ξ0}}) atTop (𝓝 0) := by sorry

end WiesemannRMDP.SRect.Supplement
