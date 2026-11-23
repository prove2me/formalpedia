-- Prove2me | Theorems.Thm_WiesemannRMDP_SRect_Supplement_lemma_C_2
-- name    : WiesemannRMDP.SRect.Supplement.lemma_C_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T10:55:42.413474+00:00
-- url     : https://prove2.me/theorems/586f85dc-2006-4d2d-b444-97f3e5e3ef33
-- title:
--   Lemma C.2 — under (A1), (A2), (A3′): the score at ξ^n vanishes w.p. → 1, n^α‖ξ^n − ξ^0‖ → 0, (1/n)∇²ℓ_n(ξ^n) → Σ in probability, Σ ≻ 0
-- statement:
--   In the setting of Theorem 5.3, assume (A1) $\xi^0\in\operatorname{int}\Xi_0$, (A2) $\widehat P(\pi_0;\xi)$ is irreducible for some $\xi\in\Xi_0$, and (A3′) the rows $[K_{sa}]^\top_{s'\cdot}$ with $\pi_0(a\mid s)>0$ have full column rank $q$. Let $(\xi^n)$ be any sequence of maximum likelihood estimators: almost surely, $\xi^n\in\Xi_0$ maximizes $\ell_n$ over $\Xi_0$. Let $\nabla_\xi\ell_n(\xi^n)$ and $\nabla^2_\xi\ell_n(\xi^n)$ be the sums (37b) and (37c), and
--   $$\Sigma := \sum_{(s,a,s')\in N_0}\frac{\pi_0(a\mid s)}{\mu_s\,p^{\xi^0}(s'\mid s,a)}\big([K_{sa}]^\top_{s'\cdot}\big)^\top[K_{sa}]^\top_{s'\cdot},\qquad N_0:=\{(s,a,s'):[k_{sa}\ K_{sa}]^\top_{s'\cdot}\ne0\}. \tag{48d}$$
--   Then
--
--   1. $\lim_{n\to\infty}\mathbb P\big(\nabla_\xi\ell_n(\xi^n)=0\big)=1$ (48a);
--   2. $\operatorname{plim}_{n\to\infty} n^\alpha\|\xi^n-\xi^0\| = 0$ for every $\alpha<1/2$ (48b);
--   3. $\operatorname{plim}_{n\to\infty}\big\|\tfrac1n\nabla^2_\xi\ell_n(\xi^n)-\Sigma\big\|=0$ (48c);
--   4. $\Sigma$ is positive definite.
--
--   These are the inputs from which the proof of Theorem 5.5 derives the uniform convergence (51) of the rescaled quadratic $\phi_n$.
--
--   **Formalization Note** Convergence in probability is `TendstoInMeasure`, which uses the outer measure of the deviation events, so the estimators need not be measurable. $\|\cdot\|$ is the sup norm on $\mathbb R^q$ in (48b) and the entrywise maximum norm on $q\times q$ matrices in (48c).
--
--   Differences from the source:
--
--   - generalization: (Ω, F, P) is the canonical space (S × A)^∞ with the product measure induced by π0 and P0 → any probability space with a process whose finite paths have the probabilities (32) at ξ0; reason: the conclusion depends only on the law of the observations, and the canonical space is one such space
--   - reading: ξn is "the" maximum likelihood estimator, which "may not be unique" (p. 31) → the lemma is stated for every sequence of almost-sure maximizers, measurable or not; reason: the paper fixes no selection, so the claim must hold for each
--   - reading: lim P(∇ξℓn(ξn) = 0) = 1 → P(∇ξℓn(ξn) ≠ 0) → 0 for the outer measure; reason: the event need not be measurable when ξn is not; for a measurable event the two are the same, and in general the Lean form implies that the inner probability of {∇ξℓn(ξn) = 0} tends to 1
--   - reading: the norms in (48b) and (48c) are not specified → the sup norm on ℝ^q and the entrywise maximum norm on matrices; reason: all norms on these finite-dimensional spaces are equivalent, so convergence in probability does not depend on the choice
--   - encoding: the observation (s1, a1, …, sn, an) → X 0, …, X (n − 1); reason: Lean's time index starts at 0
--   - reading: "the MDP" of §5.1 satisfies definition (3) → the whole of Model.Standing is assumed; reason: r, λ do not occur in Lemma C.2, so no instance is lost
-- source:
--   Wiesemann, Kuhn & Rustem, Robust Markov Decision Processes, Optimization Online 2610 (revision of February 9, 2012; sha256 8cbadb80…a79b), p. 50, Lemma C.2 (48a)–(48d); (37b), (37c) p. 34; (A1) p. 29; (A2) p. 32; (A3') p. 34

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_WiesemannRMDP_SRect_Model
import Definitions.Def_WiesemannRMDP_SRect_Supplement_Chains
import Definitions.Def_WiesemannRMDP_SRect_Supplement_Inference

open MeasureTheory ProbabilityTheory Filter FoundationsML.ReinforcementLearning Matrix
open scoped Topology ENNReal

namespace WiesemannRMDP.SRect.Supplement

open WiesemannRMDP.SRect

/-- Lemma C.2 (Wiesemann, Kuhn & Rustem, *Robust Markov Decision Processes*, Optimization Online
2610, revision of February 9, 2012, p. 50): under the assumptions (A1), (A2) and (A3'), for every
sequence `ξ_n` of maximum likelihood estimators,

* (48a) `lim_{n→∞} P(∇_ξ ℓ_n(ξ_n) = 0) = 1`;
* (48b) `plim_{n→∞} n^α ‖ξ_n − ξ0‖ = 0` for all `α < 1/2`;
* (48c) `plim_{n→∞} ‖(1/n) ∇²_ξ ℓ_n(ξ_n) − Σ‖ = 0`, with `∇_ξ ℓ_n(ξ_n)`, `∇²_ξ ℓ_n(ξ_n)` the sums
  (37b), (37c) and `Σ` the matrix (48d);
* moreover, the matrix `Σ` is positive definite.

**Formalization Note.** Convergence in probability is `TendstoInMeasure` (outer measure of the
deviation events, so no measurability of `ξ_n` is needed). (48a) is stated as
`P(∇_ξ ℓ_n(ξ_n) ≠ 0) → 0` for the outer measure, which gives `P(∇_ξ ℓ_n(ξ_n) = 0) → 1` and is the
same statement for a measurable event. `‖·‖` in (48b) is the sup norm on `ℝ^q`, and in (48c) the
entrywise maximum norm on `q × q` matrices (all norms on these finite-dimensional spaces give
the same convergence in probability). -/
theorem lemma_C_2 {St Act : Type*} [Fintype St] [DecidableEq St] [Fintype Act]
    [DecidableEq Act] [Nonempty St] [Nonempty Act] {q L : ℕ} (M : Model St Act q L)
    (hM : M.Standing) (π0 : St → Act → ℝ) (hπ0 : IsPolicy π0)
    (ξ0 : Fin q → ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → St × Act) (hX : IsObservationProcess M π0 ξ0 P X)
    (hA1 : A1 M ξ0) (hA2 : A2 M π0) (hA3' : A3' M π0)
    (ξhat : ℕ → Ω → Fin q → ℝ) (hξhat : IsMLESeq M π0 X P ξhat) :
    Tendsto (fun n => P {ω | scoreVec M X n ω (ξhat n ω) ≠ 0}) atTop (𝓝 0) ∧
    (∀ α : ℝ, α < 1 / 2 →
      TendstoInMeasure P (fun (n : ℕ) ω => (n : ℝ) ^ α * ‖ξhat n ω - ξ0‖) atTop (fun _ => 0)) ∧
    TendstoInMeasure P
      (fun (n : ℕ) ω => (fun u v => (1 / (n : ℝ)) * infoMat M X n ω (ξhat n ω) u v :
        Fin q → Fin q → ℝ))
      atTop (fun _ => (fun u v => sigmaMat M π0 ξ0 u v : Fin q → Fin q → ℝ)) ∧
    (sigmaMat M π0 ξ0).PosDef := by sorry

end WiesemannRMDP.SRect.Supplement
