-- Prove2me | Theorems.Thm_TimeVaryingGames_proposition_1
-- name    : TimeVaryingGames.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:31:34.637599+00:00
-- url     : https://prove2.me/theorems/8a445a4b-07e5-4f51-829d-2121923e7f28
-- title:
--   Proposition 1, p.17: the energy $E_t$ converges almost surely to an integrable $E_\infty$
-- statement:
--   Let $x^*$ be the Nash equilibrium of the limit game and $E_t=\sum_i D_i(x^*_i,X_{i,t})/\lambda_i$ the energy of the iterates, with $\lambda_i=(\prod_j\lambda_{ij})^{1/N}$. Then $E_t$ converges almost surely to a random variable $E_\infty$ with $\mathbb E[E_\infty]<\infty$.
--
--
--   The setting is that of Theorem 1: finitely many players with nonempty compact convex action sets in finite-dimensional normed spaces; stage games $\mathcal G_t$ satisfying Assumption 1 and converging ($R_{i,t}\to0$) to a strictly monotone limit game $\mathcal G$ with $C^1$ payoffs; every player runs mirror descent with a DGF $h_i$, from a deterministic point of the prox-domain, on oracle signals $V_{i,t}=v_{i,t}(X_t)+Z_{i,t}$ whose bias, variance and second moment satisfy (9a)–(9c) with deterministic bounds ($B$ non-increasing, $\sigma,M$ non-decreasing); the step sizes are positive, non-increasing and satisfy (S1), (S2) with constants $\lambda_{ij}>0$, and (S3):
--   $$\sum_t\gamma_{i,t}(R_{i,t}+B_{i,t})<\infty,\qquad\sum_t\gamma_{i,t}^2(M_{i,t}^2+\sigma_{i,t}^2)<\infty.$$
--
--   The proposition is the stochastic half of the convergence proof: the energy settles down, although a priori not to $0$. The reciprocity condition (RC) is not needed here.
--
--   **Formalization Note** $\mathbb E[E_\infty]<\infty$ is stated as integrability of $E_\infty$ (the limit is nonnegative).
--
--   Differences from the source:
--   - encoding: x∗ the (unique) Nash equilibrium of G → a parameter xs with IsNash K uLim xs; reason: the limit game's equilibrium is unique, so the statement is about the same point
--   - encoding: E_t converges a.s. to a random variable E_∞ with E[E_∞] < ∞ → ∃ Einf, Integrable Einf P ∧ a.s. E_t → Einf; reason: for the nonnegative limit, integrability is E[E_∞] < ∞ (and includes measurability)
--   - generalization: F_t = σ(X_1, …, X_t), the natural filtration, with (8)–(9) relative to it → any filtration ℱ to which X is (strongly) adapted, with (8)–(9) relative to ℱ; reason: the natural filtration of X is an instance of ℱ
--   - generalization: X_1 = arg min h (Algorithm 1) → X 0 = x₁ for any deterministic x₁ with each x₁ i in the prox-domain of h_i; reason: arg min h lies in the prox-domain (0 ∈ ∂h there; proved in the verification file)
--   - reading: the evolution of G_t "could be random" (p.6) → one fixed deterministic sequence of stage games; reason: (17) and (S3) are deterministic conditions on R_{i,t}, the proof of Proposition 1 takes ρ_t to be F_t-measurable with F_t = σ(X_1, …, X_t) (p.18), and for a random G_t the Remark after Theorem 4 (p.28) enlarges F_t while its proof moves the game randomness into the oracle error and applies Theorem 1 to a fixed sequence
--   - encoding: stages t = 1, 2, … → t : ℕ starting at 0 (Lean's t is stage t + 1); reason: index shift; same sequences
--   - encoding: h : X → ℝ ∪ {∞} with dom h = C; ∂h(x) tested against all x′ ∈ X → h : E → ℝ with only its values on C used; the subgradient inequality tested for x′ ∈ C; reason: h = +∞ off C, so the inequality is automatic off C: the same subdifferential and prox-domain
--   - encoding: there exists a continuous selection ∇h of ∂h on dom ∂h → the selection is a parameter gradh with ContinuousOn and gradh x ∈ ∂h(x) on the prox-domain; reason: D and P are defined through the selection, so it must be fixed data
--   - encoding: the tacit open neighbourhood of K (p.4) for the limit game and for each stage game → explicit open sets ULim and UStage t containing K, a separate one per game; reason: the paper's own device, made explicit
--   - encoding: the prox-mapping P(x; y) = argmin (13) as a function → the relation IsProxPoint (xp ∈ C minimizes (13)); reason: the minimizer exists and is unique for a DGF, so the relation is the graph of P
--   - encoding: (S2) holds for some λ_ij > 0 → a family lam : ι → ι → ℝ with lam i j > 0 as a parameter; reason: choosing the witnesses of the existential once for all pairs
--   - encoding: (9) presupposes the conditional expectations exist → V strongly measurable with ‖V_{i,t}‖² integrable; 0 ≤ σ_{i,t}, 0 ≤ M_{i,t}; reason: Lean's conditional expectation of a non-integrable function is 0; nothing the paper allows is excluded
--   - encoding: (9a) ‖b_{i,t}‖_* ≤ B_{i,t} → almost surely ‖b_{i,t}‖_* ≤ B_{i,t}; reason: b_{i,t} is a conditional expectation, defined up to a null set
--   - encoding: Σ_t γ_{i,t} = ∞ for positive γ_{i,t} → ¬ Summable (γ i); reason: for positive terms, non-summability is divergence to +∞
--   - encoding: K-strongly convex with modulus K (divided by in (A.5b), (40)) → 0 < Kc is part of IsDGF; reason: a strong-convexity modulus is positive; the paper divides by it
--   - encoding: profile norm ‖x‖² = Σ_i ‖x_i‖² in (4b) → Real.sqrt (∑ j, ‖x' j − x j‖ ^ 2) written out; reason: Lean's product norm is the sup norm
--   - encoding: R_{i,t} = max_{x∈K} ‖v_{i,t}(x) − v_i(x)‖_* → a real ⨆ over the subtype of profiles; reason: the subtype is nonempty and the function bounded (by (4a) and continuity of v on compact K), so the ⨆ is the maximum
--   - encoding: S²_{i,t} in (S3) → M i t ^ 2 + σ i t ^ 2; reason: definition (9d)
--   - encoding: N = {1, …, N} players, compact convex K_i → Nonempty ι (and, where existence matters, nonempty K_i); reason: nondegeneracy implicit in the paper: a game has a player and every player has an action
--   - encoding: Σ_t a_t < ∞ for the nonnegative series of (S2), (S3) → Summable; reason: for nonnegative terms, a finite sum is summability
-- source:
--   Duvocelle, Mertikopoulos, Staudigl, Vermeulen, Multi-Agent Online Learning in Time-Varying Games, arXiv:1809.03066v3, Proposition 1, p.17, in the setting of Theorem 1, p.10

import Mathlib
import Definitions.Def_TimeVaryingGames_ContinuousGame
import Definitions.Def_TimeVaryingGames_DGF
import Definitions.Def_TimeVaryingGames_StageGames
import Definitions.Def_TimeVaryingGames_MirrorDescent
import Definitions.Def_TimeVaryingGames_Weights

open MeasureTheory Filter Topology

namespace TimeVaryingGames

/-- **Proposition 1 (the energy converges almost surely).**
arXiv:1809.03066v3, §4.3, p.17: "Proposition 1. Suppose that each player i ∈ N runs Algorithm 1
with a step-size γ_{i,t} satisfying (S1), (S2) and (S3). Then E_t converges (a.s.) to a random
variable E_∞ with E[E_∞] < ∞."

Setting: that of Theorem 1 (§4.1, §4.3): the stage games satisfy Assumption 1 and converge (18)
to a strictly monotone limit game `G`, and `E_t = E(X_t)` is the energy (39) relative to the Nash
equilibrium `x*` of `G` and the weights `λ_i` of (34). (RC) is not among the hypotheses, as in the
paper's statement.

Conclusion: there is an integrable random variable `E_∞` (so `E[E_∞] < ∞`) with `E_t → E_∞`
almost surely.

**Formalization Note.** Lean's `t : ℕ` is the paper's stage `t + 1`. Action spaces are
finite-dimensional normed spaces (no inner product); payoff gradients are elements of the dual
`E i →L[ℝ] ℝ`, whose operator norm is `‖·‖_*`. `F_t` is any filtration `ℱ` to which the iterates are
adapted, and (8)–(9) are taken relative to it (the natural filtration `σ(X_1, …, X_t)` is one such);
`X_1 = X 0` is any deterministic point of the prox-domains (the paper's `arg min h` is one). The
stage games are one fixed (deterministic) sequence. `S²_{i,t} = M²_{i,t} + σ²_{i,t}` is (9d). The
constants `λ_{ij}` of (S2) are the parameter `lam`. The DGF selection `∇h_i` is the parameter
`gradh i`, and the prox-mapping is the relation `IsProxPoint`. -/
theorem proposition_1 {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)] [∀ i, FiniteDimensional ℝ (E i)]
    -- the action sets
    (K : ∀ i, Set (E i)) (hKne : ∀ i, (K i).Nonempty) (hKc : ∀ i, IsCompact (K i))
    (hKcv : ∀ i, Convex ℝ (K i))
    -- the limit game `G`: C¹ payoffs on an open neighbourhood of `K`, strictly monotone
    (uLim : ι → (∀ j, E j) → ℝ) (ULim : Set (∀ j, E j)) (hULim : IsOpen ULim)
    (hKULim : profiles K ⊆ ULim) (huLim : ∀ i, ContDiffOn ℝ 1 (uLim i) ULim)
    (hmono : IsStrictlyMonotone K uLim)
    -- the stage games `G_t`: Assumption 1, and convergence (18) to `G`
    (uStage : ℕ → ι → (∀ j, E j) → ℝ) (UStage : ℕ → Set (∀ j, E j)) (G L : ι → ℝ)
    (hA1 : Assumption1 K UStage uStage G L)
    (hconv : ∀ i, Tendsto (fun t => stabilizationGap K uStage uLim i t) atTop (𝓝 0))
    -- the players' DGFs (Definition 1)
    (Kc : ι → ℝ) (h : ∀ i, E i → ℝ) (gradh : ∀ i, E i → E i →L[ℝ] ℝ)
    (hdgf : ∀ i, IsDGF (K i) (Kc i) (h i) (gradh i))
    -- the probability space, the filtration, the iterates and the oracle signals
    {Ω : Type*} {m₀ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ m₀) (X : ℕ → Ω → ∀ i, E i) (hXad : StronglyAdapted ℱ X)
    (V : ∀ i, ℕ → Ω → E i →L[ℝ] ℝ)
    -- Algorithm 1 from a deterministic initial point
    (γ : ι → ℕ → ℝ) (x₁ : ∀ i, E i) (hX0 : ∀ ω, X 0 ω = x₁)
    (hrun : ∀ ω, IsMDPath K h gradh γ (fun i t => V i t ω) (fun t => X t ω))
    -- the oracle statistics (9a)–(9c) and the monotonicity of their bounds
    (B σ M : ι → ℕ → ℝ) (hσ : ∀ i t, 0 ≤ σ i t) (hM : ∀ i t, 0 ≤ M i t)
    (hBanti : ∀ i, Antitone (B i)) (hσmono : ∀ i, Monotone (σ i)) (hMmono : ∀ i, Monotone (M i))
    (horacle : OracleStatistics P ℱ X V uStage B σ M)
    -- the step sizes: positive, non-increasing, (S1), (S2), (S3)
    (hγpos : ∀ i t, 0 < γ i t) (hγanti : ∀ i, Antitone (γ i))
    (hS1 : ∀ i, ¬ Summable (γ i))
    (lam : ι → ι → ℝ) (hlam : ∀ i j, 0 < lam i j)
    (hS2 : ∀ i j, Summable fun t => |γ i t - lam i j * γ j t|)
    (hS3R : ∀ i, Summable fun t => γ i t * (stabilizationGap K uStage uLim i t + B i t))
    (hS3S : ∀ i, Summable fun t => γ i t ^ 2 * (M i t ^ 2 + σ i t ^ 2))
    (xs : ∀ i, E i) (hxs : IsNash K uLim xs)
    :
    ∃ Einf : Ω → ℝ, Integrable Einf P ∧
      ∀ᵐ ω ∂P, Tendsto (fun t => energy h gradh lam xs (X t ω)) atTop (𝓝 (Einf ω)) := by sorry

end TimeVaryingGames
