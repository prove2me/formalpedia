-- Prove2me | Theorems.Thm_SmallLossGraph_theorem_3_6
-- name    : SmallLossGraph.theorem_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:55:24.505104+00:00
-- url     : https://prove2.me/theorems/85ed5290-d6fc-424a-bc01-6290744676f5
-- title:
--   Theorem 3.6 (corrected: constant 300, not 100) — Double-Threshold Freezing has $\varepsilon$-approximate regret $\le 300\alpha(A(d,T)+3\log\frac{d+2}{\delta})/\varepsilon^2$ w.p. $1-\delta$
-- statement:
--   Let $\varepsilon>0$, $\delta>0$ and $\varepsilon'=\varepsilon/5$. Consider $d$ arms, $T$ rounds and an adaptive adversary that chooses in every round an undirected feedback graph $G^t$ and losses $\ell^t\in[0,1]^d$, where every independent set of every $G^t$ has at most $\alpha$ vertices. Let $A$ be a full-information algorithm whose approximate regret, on losses in $[0,L]$ with $L=1/\gamma'=12\alpha/\varepsilon'$ and horizon $T$, is bounded against every arm $f$:
--
--   $$
--   (1-\varepsilon')\sum_t\sum_ip^t_i\ell^t_i-\sum_t\ell^t_f\le\frac{L\cdot A(d,T)}{\varepsilon'}=\frac{5L\cdot A(d,T)}{\varepsilon}.
--   $$
--
--   Run the Double-Threshold Freezing Algorithm (Algorithm 1) with learning parameter $\varepsilon'$ on $A$, $\alpha$, $d$. Then, with probability at least $1-\delta$, simultaneously for every arm $f$,
--
--   $$
--   \mathrm{ApxReg}(f,\varepsilon)=(1-\varepsilon)\sum_t\ell^t_{I(t)}-\sum_t\ell^t_f\le\frac{300\,\alpha\,\big(A(d,T)+3\log\frac{d+2}{\delta}\big)}{\varepsilon^2}.
--   $$
--
--   This is the paper's black-box reduction: any full-information learner with a small-loss (approximate-regret) guarantee becomes a learner under graph feedback whose approximate regret depends on the independence number $\alpha$ instead of the number of arms, with high probability.
--
--   **The printed constant is $100$; it is false.** Take $d=2$, complete graphs in every round (so $\alpha=1$), $\varepsilon=\delta=1/2$ and the losses $(1,0)$ in every round. Let $A$ put all its mass on arm $1$ while its running approximate regret allows one more round of the maximal loss $L=120$ within the budget $L(A(d,T)-\frac12\ln2)/\varepsilon'$ with $A(d,T)=20$, and run Hedge with rate $2\varepsilon'/L$ afterwards; it satisfies the hypothesis. On complete graphs nothing is frozen, so arm $1$ is played for $26\,085$ rounds deterministically and, with $T=26\,085$, $\mathrm{ApxReg}(2,\varepsilon)=13\,042.5$ with probability $1$, while the printed bound is $100(20+3\ln8)/0.25\approx10\,495$. The paper's proof bounds the estimated losses by $1/\gamma$ where only $1/\gamma'=3/\gamma$ holds (proof of Theorem 3.4); carried through with $1/\gamma'$ it gives $300$, and the same family of instances ($\varepsilon\to0$, $A(d,T)\to\infty$) shows that no constant below $300$ works.
--
--   Differences from the source:
--   - correction: ApxReg(f, ε) ≤ 100α(A(d,T) + 3 log((d+2)/δ))/ε² → the same bound with 300 in place of 100; reason: counterexample d = 2, complete graphs, α = 1, ε = δ = 1/2, losses (1, 0), an A with A(d,T) = 20 that spends its regret budget on arm 1 and then runs Hedge: ApxReg(2, ε) = 13042.5 > 10495 with probability 1 at T = 26085; the proof uses the range 1/γ for 1/γ′, and 300 is the least constant of this form
--   - reading: with probability 1 − δ, ApxReg(f, ε) ≤ … (f not quantified inside the probability) → Pr[∃ f, ApxReg(f, ε) > bound] ≤ δ, all arms simultaneously; reason: the proof's union bound over d + 2 events (δ′ = δ/(d+2)) covers every arm f
--   - reading: A has expected approximate regret ≤ 5L·A(d,T)/ε when run on losses in [0, L] → deterministic A, told its range L, with (1 − ε′)Σ_tΣ_i p^t_iℓ^t_i − Σ_tℓ^t_f ≤ L·A(d,T)/ε′ for every loss sequence in [0, L]; reason: Algorithm 1 uses only A's vector p^t, and the proofs apply A's bound to Σ_tΣ_i p^t_iℓ̃^t_i; A is instantiated with its range as Multiplicative Weights is in Corollary 3.5
--   - generalization: A's guarantee for every ε and every L → A's guarantee only at ε′ = ε/5, L = 1/γ′ = 12α/ε′ and horizon T; reason: the proof invokes the guarantee only there; an A with the guarantee for all ε, L satisfies it
--   - encoding: adaptive adversary choosing G^t and ℓ^t; α(G^t) ≤ α for every round → deterministic map from the earlier arms to (G^t, ℓ^t), with every graph it can output bounded by α; reason: randomized adversaries are mixtures of deterministic ones; graphs on histories the run never reaches do not affect it
--   - encoding: α an input upper bound on independent sets, with α ≥ 1, d ≥ 1 implicit → α : ℕ with the independence bound; no separate 0 < α or d ≥ 1; reason: a full-information algorithm outputs probability vectors, so d ≥ 1, and then a single arm is an independent set, so α ≥ 1
--   - encoding: rounds 1, …, T; log; probability of the run → rounds 0, …, T − 1; Real.log (natural log); sum of path probabilities ∏_t w^t_{I(t)}; reason: Lean conventions; same instances
--   - encoding: Algorithm 1, line 5, divides by 1 − Σ_{j∈F} p_j, undefined when every arm carrying probability is frozen → in that case w = p (sampling convention); reason: the case cannot occur for ε′ < 1 (Lemma 3.1), so no instance of the paper changes; the convention keeps w a probability vector
-- source:
--   Lykouris–Sridharan–Tardos, Small-loss bounds for online learning with partial information, arXiv:1711.03639v5, Theorem 3.6, p.12 (proof pp.12–13)

import Mathlib
import Definitions.Def_SmallLossGraph_Protocol
import Definitions.Def_SmallLossGraph_Freezing
import Definitions.Def_SmallLossGraph_Run

open scoped BigOperators

namespace SmallLossGraph

/-- **Theorem 3.6 (corrected constant 300): high-probability approximate regret of the
Double-Threshold Freezing Algorithm.**
Lykouris–Sridharan–Tardos, arXiv:1711.03639v5, Theorem 3.6, p.12: "Let `A` be any full
information algorithm with an expected approximate regret guarantee of:
`E[ApxReg(f, ε/5)] ≤ 5L·A(d,T)/ε`, against any arm `f`, when run on losses in `[0, L]`. For any
`δ > 0`, with probability `1−δ`, the Double-Threshold Freezing Algorithm (Algorithm 1) run with
learning parameter `ε′ = ε/5` on input `A`, `α`, `d`, has `ε`-approximate regret of:
`ApxReg(f, ε) ≤ 100α · (A(d, T) + 3 log((d + 2)/δ))/ε²`."

Let `ε > 0`, `δ > 0`, let `adv` be an adaptive adversary all of whose feedback graphs have
independent sets of at most `α` vertices, and let `A` be a full-information algorithm whose
approximate regret at parameter `ε′ = ε/5`, on losses in `[0, L]` with `L = 1/γ′ = 12α/ε′`
(the range of the estimated losses) and horizon `T`, is at most `L·A(d,T)/ε′` against every arm.
Then Algorithm 1 run with `ε′ = ε/5` on `A`, `α`, `d` satisfies
`Pr[ ∃ f, ApxReg(f, ε) > 300α (A(d,T) + 3 log((d+2)/δ))/ε² ] ≤ δ`.

**Formalization Note** The printed constant `100` is false (counterexample: `d = 2`, complete
graphs, `α = 1`, `ε = δ = 1/2`, losses `(1, 0)`, an `A` with `A(d,T) = 20` that spends its
regret budget on arm 1 first, then runs Hedge: `ApxReg(2, ε) = 13042.5 > 10495` with
probability `1` for `T = 26085`); the paper's proof, using the estimator range `1/γ′` (proof of
Theorem 3.4) instead of `1/γ`, gives `300`, the least constant of this form. The bound holds for
all comparator arms simultaneously. `A(d,T)` is the real `Abound`; `A` is deterministic and its
guarantee is assumed only at `ε′ = ε/5`, `L = 1/γ′` and horizon `T`. The adversary is
deterministic and adaptive; rounds are 0-based; `log` is natural. -/
theorem theorem_3_6 {d : ℕ} (T : ℕ) (α : ℕ) (ε δ Abound : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (A : FullInfoAlg d) (hA : HasApxRegretBound A T (ε / 5) (1 / gammaPrime (ε / 5) α) Abound)
    (adv : Adversary d) (hα : ∀ h, IndepBound (adv.graph h) α) :
    probEvent T A adv (ε / 5) α (fun s => ∃ f : Fin d,
        300 * (α : ℝ) * (Abound + 3 * Real.log (((d : ℝ) + 2) / δ)) / ε ^ 2 < apxReg adv s f ε)
      ≤ δ := by sorry

end SmallLossGraph
