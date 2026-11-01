-- Prove2me | Theorems.Thm_TimeVaryingGames_lemma_2
-- name    : TimeVaryingGames.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:31:12.315832+00:00
-- url     : https://prove2.me/theorems/7585d8da-c0d9-441b-baf7-4b4c42ed0b03
-- title:
--   Lemma 2, p.16: the energy inequality (40)
-- statement:
--   Consider finitely many players, each with a DGF $h_i$ of modulus $K_i$ on a compact convex action set $\mathcal K_i$, running mirror descent $X_{i,t+1}=\mathcal P_i(X_{i,t};\gamma_{i,t}V_{i,t})$ from a point of the prox-domains, with step sizes $\gamma_{i,t}>0$ satisfying (S1) and (S2) with constants $\lambda_{ij}>0$. Let $\lambda_i$, $\gamma_t$ and $E$ be the speeds, effective step and energy (relative to a profile $x^*\in\mathcal K$), let $v$ be the payoff gradient of a limit game with $\|v_i(x)\|_*\le G_i$ on $\mathcal K$, $v_t$ that of a stage game, $Z_{i,t}=V_{i,t}-v_{i,t}(X_t)$ and $r_{i,t}=v_{i,t}(X_t)-v_i(X_t)$. Then $E_t=E(X_t)$ satisfies
--   $$E_{t+1}\le E_t+\gamma_t\langle v(X_t),X_t-x^*\rangle+\sum_{i}\frac{\gamma_{i,t}}{\lambda_i}\langle r_{i,t}+Z_{i,t},X_{i,t}-x^*_i\rangle+\sum_i\frac{\gamma_{i,t}^2}{2\lambda_iK_i}\|V_{i,t}\|_*^2+\frac{\max_iG_i\operatorname{diam}(\mathcal K_i)}{N}\sum_{i,j}\Big|\frac{\gamma_{i,t}}{\lambda_i}-\frac{\gamma_{j,t}}{\lambda_j}\Big|.$$
--
--   This quasi-descent inequality is the engine of the convergence proof: the drift term is nonpositive at a Nash equilibrium of a monotone game, and every other term is summable under (S2)–(S3).
--
--   **Formalization Note** The inequality is pathwise, so it is stated for an arbitrary sequence of signals. $\max_i$ is a finite maximum over the players and $\operatorname{diam}$ is the metric diameter, finite since $\mathcal K_i$ is compact.
--
--   Differences from the source:
--   - generalization: x∗ the Nash equilibrium of G → any profile xs ∈ K; reason: the bound (40) never uses the equilibrium property; the paper's x∗ is such a profile
--   - generalization: G_i from Assumption 1 applied to the limit game (used in (43)), and C¹/C² payoffs → any constants G_i with ‖v_i(x)‖_* ≤ G_i on K; no regularity of the payoffs; reason: Assumption 1 and (18) give this bound with the paper's G_i, and the inequality uses nothing else about the payoffs
--   - generalization: random oracle signals V_{i,t} and the run of Algorithm 1 from X_1 = arg min h → any sequence of dual vectors V and any mirror-descent path from a point of the prox-domains; reason: the inequality is pathwise; arg min h is in the prox-domain
--   - generalization: γ_{i,t} non-increasing, assumed throughout (p.7, item 4) → no monotonicity of γ i is assumed; only 0 < γ i t; reason: the pathwise bound (41)–(43) never uses monotonicity of the step sizes; non-increasing step sizes are an instance
--   - encoding: stages t = 1, 2, … → t : ℕ starting at 0 (Lean's t is stage t + 1); reason: index shift; same sequences
--   - encoding: (S2) holds for some λ_ij > 0 → a family lam : ι → ι → ℝ with lam i j > 0 as a parameter; reason: choosing the witnesses of the existential once for all pairs
--   - encoding: Σ_t γ_{i,t} = ∞ for positive γ_{i,t} → ¬ Summable (γ i); reason: for positive terms, non-summability is divergence to +∞
--   - encoding: h : X → ℝ ∪ {∞} with dom h = C; ∂h(x) tested against all x′ ∈ X → h : E → ℝ with only its values on C used; the subgradient inequality tested for x′ ∈ C; reason: h = +∞ off C, so the inequality is automatic off C: the same subdifferential and prox-domain
--   - encoding: there exists a continuous selection ∇h of ∂h on dom ∂h → the selection is a parameter gradh with ContinuousOn and gradh x ∈ ∂h(x) on the prox-domain; reason: D and P are defined through the selection, so it must be fixed data
--   - encoding: the prox-mapping P(x; y) = argmin (13) as a function → the relation IsProxPoint (xp ∈ C minimizes (13)); reason: the minimizer exists and is unique for a DGF, so the relation is the graph of P
--   - encoding: K-strongly convex with modulus K (divided by in (A.5b), (40)) → 0 < Kc is part of IsDGF; reason: a strong-convexity modulus is positive; the paper divides by it
--   - encoding: N = {1, …, N} players, compact convex K_i → Nonempty ι (and, where existence matters, nonempty K_i); reason: nondegeneracy implicit in the paper: a game has a player and every player has an action
--   - encoding: Σ_t a_t < ∞ for the nonnegative series of (S2), (S3) → Summable; reason: for nonnegative terms, a finite sum is summability
-- source:
--   Duvocelle, Mertikopoulos, Staudigl, Vermeulen, Multi-Agent Online Learning in Time-Varying Games, arXiv:1809.03066v3, Lemma 2, p.16, eq. (40), with (34), p.15, (38)–(39), p.16, and (43), p.17

import Mathlib
import Definitions.Def_TimeVaryingGames_ContinuousGame
import Definitions.Def_TimeVaryingGames_MirrorDescent
import Definitions.Def_TimeVaryingGames_Weights

namespace TimeVaryingGames

/-- **Lemma 2 (energy inequality).**
arXiv:1809.03066v3, §4.3, p.16: "Lemma 2. Suppose that each player i ∈ N runs Algorithm 1 with a
step-size policy γ_{i,t} satisfying (S1) and (S2). Then the iterates E_t := E(X_t) of E under X_t
enjoy the bound
E_{t+1} ≤ E_t + γ_t⟨v(X_t), X_t − x*⟩ + Σ_{i∈N} (γ_{i,t}/λ_i)⟨r_{i,t} + Z_{i,t}, X_{i,t} − x*_i⟩
+ Σ_{i∈N} (γ²_{i,t}/(2λ_iK_i))‖V_{i,t}‖²_* + (max_i G_i diam(K_i)/N) Σ_{i,j∈N} |γ_{i,t}/λ_i − γ_{j,t}/λ_j| (40)
with r_{i,t} = v_{i,t}(X_t) − v_i(X_t)."

Here `E = energy` (39) relative to `x*`, `γ_t = effectiveStep` (38), `λ_i = speed lam i` (34),
`K_i` the modulus of player `i`'s DGF, `v` the limit game's and `v_t` the stage game's payoff
gradient, `Z_{i,t} = V_{i,t} − v_{i,t}(X_t)` (SFO), and `G_i` a bound on `‖v_i‖_*` over the action
space (as used in (43)).

**Formalization Note.** The inequality is pathwise: it holds for every realization, so it is
stated for an arbitrary sequence of signals `V` and the resulting mirror-descent path `X`. The
reference profile `x*` is any action profile (the proof does not use that it is a Nash
equilibrium), and the bound `G_i` on the limit gradient is a hypothesis (in the paper it comes from
Assumption 1 and (18)). `max_i` is `Finset.sup'` over the (nonempty) player set. -/
theorem lemma_2 {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)] [∀ i, FiniteDimensional ℝ (E i)]
    (K : ∀ i, Set (E i)) (Kc : ι → ℝ) (h : ∀ i, E i → ℝ) (gradh : ∀ i, E i → E i →L[ℝ] ℝ)
    (hdgf : ∀ i, IsDGF (K i) (Kc i) (h i) (gradh i))
    (uLim : ι → (∀ j, E j) → ℝ) (G : ι → ℝ)
    (hG : ∀ i, ∀ x ∈ profiles K, ‖partialGradient uLim i x‖ ≤ G i)
    (uStage : ℕ → ι → (∀ j, E j) → ℝ)
    (γ : ι → ℕ → ℝ) (hγ : ∀ i t, 0 < γ i t) (hS1 : ∀ i, ¬ Summable (γ i))
    (lam : ι → ι → ℝ) (hlam : ∀ i j, 0 < lam i j)
    (hS2 : ∀ i j, Summable fun t => |γ i t - lam i j * γ j t|)
    (V : ∀ i, ℕ → E i →L[ℝ] ℝ) (X : ℕ → ∀ i, E i) (hrun : IsMDPath K h gradh γ V X)
    (xs : ∀ i, E i) (hxs : xs ∈ profiles K) (t : ℕ) :
    energy h gradh lam xs (X (t + 1)) ≤
      energy h gradh lam xs (X t)
        + effectiveStep lam γ t * ∑ i, partialGradient uLim i (X t) (X t i - xs i)
        + ∑ i, γ i t / speed lam i *
            ((partialGradient (uStage t) i (X t) - partialGradient uLim i (X t))
              + (V i t - partialGradient (uStage t) i (X t))) (X t i - xs i)
        + ∑ i, γ i t ^ 2 / (2 * speed lam i * Kc i) * ‖V i t‖ ^ 2
        + Finset.univ.sup' Finset.univ_nonempty (fun i => G i * Metric.diam (K i))
            / (Fintype.card ι : ℝ)
            * ∑ i, ∑ j, |γ i t / speed lam i - γ j t / speed lam j| := by sorry

end TimeVaryingGames
