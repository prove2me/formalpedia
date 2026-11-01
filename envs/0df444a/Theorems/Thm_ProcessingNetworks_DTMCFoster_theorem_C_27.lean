-- Prove2me | Theorems.Thm_ProcessingNetworks_DTMCFoster_theorem_C_27
-- name    : ProcessingNetworks.DTMCFoster.theorem_C_27
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:26:51.510565+00:00
-- url     : https://prove2.me/theorems/84568bb3-76dc-4e2f-8b74-92767ab03205
-- title:
--   Theorem C.27 (State-dependent Foster–Lyapunov criterion) — $\mathbb E_x V(X_{n(x)})\le V(x)-n(x)+b1_C(x)$ implies positive recurrence
-- statement:
--   Let $X$ be an irreducible discrete-time Markov chain on a countable state space $\mathcal S$ with transition matrix $P$. Suppose there exist a constant $b>0$, a finite set $C\subseteq\mathcal S$, a function $n:\mathcal S\to\{1,2,\dots\}$ and a non-negative function $V:\mathcal S\to\mathbb R_+$ such that
--   $$
--   \mathbb E_x\big(V(X_{n(x)})\big)\le V(x)-n(x)+b\,1_C(x),\qquad x\in\mathcal S, \tag{C.24}
--   $$
--   where $\mathbb E_x\big(V(X_m)\big)=\sum_{y\in\mathcal S}P^m_{xy}V(y)$ is the expectation of $V$ after $m$ steps from $x$. Then $X$ is positive recurrent: $\mathbb E_i(\tau_i)<\infty$ for every state $i$, where $\tau_i=\inf\{k\ge1:X_k=i\}$.
--
--   Unlike the standard criterion (Theorem C.26, the case $n\equiv1$), the drift is measured over a number of steps $n(x)$ that may depend on the state and be unbounded, and the required decrease is proportional to that number of steps. The book uses this version, not the standard one, to prove its fluid-model stability lemma (Lemma 3.7).
--
--   **Formalization Note** The chain is its transition matrix $P:S\to\mathrm{PMF}(S)$, and $P^m_{xy}$ is the platform's $m$-step probability `transitionPower P m x y`.
--
--   Differences from the source:
--   - encoding: a DTMC X on a countable state space 𝒮 with transition matrix P → the transition matrix P : S → PMF S (Chain S) on a type S with [Countable S]; reason: the statement depends on X only through P (and the initial state); a countable type covers the book's finite or countable 𝒮 (p.275)
--   - encoding: E_x(V(X_{n(x)})) ≤ V(x) − n(x) + b1_C(x) (C.24), real inequality → Σ_y P^{n(x)}(x, y) V(y) + n(x) ≤ V(x) + b·1_C(x) in [0, ∞], with P^m = transitionPower P m; reason: E_x V(X_m) = Σ_y P^m(x, y) V(y); the book's right side is finite, so (C.24) forces the expectation to be finite and the two forms are equivalent
--   - encoding: n : 𝒮 → {1, 2, …}, V : 𝒮 → ℝ₊, b > 0 → n : S → ℕ with 1 ≤ n x for all x, V : S → ℝ≥0, b : ℝ≥0 with 0 < b; reason: same instances
--   - encoding: X is positive recurrent (Def C.16) → PositiveRecurrent P: meanReturn P {i} i = E_i(τ_i) < ∞ for every state i; reason: Def C.16 applied to every state; a finite mean return time already makes the state recurrent
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability (pre-publication draft 2020-4-2, spnbook.org), Appendix C, §C.8, Theorem C.27 (C.24), p.284 (PDF p.300)

import Definitions.Def_KellyStochasticNetworks_MaxWeight_Chain

open scoped ENNReal NNReal
open KellyStochasticNetworks.MaxWeight

namespace ProcessingNetworks.DTMCFoster

/-- **Theorem C.27** (State-dependent Foster-Lyapunov criterion), Dai & Harrison, *Processing
Networks*, pre-publication draft 2020-4-2, spnbook.org, Appendix C, §C.8, p.284, PDF p.300:
"Assume that the DTMC `X` is irreducible. Suppose there exists a constant `b > 0`, a finite set
`C ⊂ 𝒮`, a function `n : 𝒮 → {1, 2, …}`, and a non-negative function `V : 𝒮 → ℝ₊` such that
`E_x(V(X_{n(x)})) ≤ V(x) − n(x) + b 1_C(x)`, `x ∈ 𝒮` (C.24). Then `X` is positive recurrent."

**Formalization Note** The chain is its transition matrix `P : S → PMF S` (`Chain S`) on a
countable type `S`; `E_x(V(X_m)) = Σ_y P^m(x, y) V(y)` with the `m`-step probabilities
`transitionPower P m x y`. (C.24) is written additively in `[0, ∞]`,
`Σ_y P^{n(x)}(x, y) V(y) + n(x) ≤ V(x) + b 1_C(x)`, which is the book's inequality (its right side is
finite, so it forces the expectation to be finite). `n` is `ℕ`-valued with `n(x) ≥ 1`; `b` is a
positive element of `ℝ≥0`. `PositiveRecurrent P` says `E_i(τᵢ) < ∞` for every state `i`
(Def C.16 at every state). -/
theorem theorem_C_27 {S : Type*} [Countable S] (P : Chain S) (hirr : Irreducible P)
    (b : ℝ≥0) (hb : 0 < b) (C : Set S) (hC : C.Finite)
    (n : S → ℕ) (hn : ∀ x, 1 ≤ n x) (V : S → ℝ≥0)
    (hdrift : ∀ x, (∑' y, transitionPower P (n x) x y * (V y : ℝ≥0∞)) + (n x : ℝ≥0∞) ≤
      V x + C.indicator (fun _ => (b : ℝ≥0∞)) x) :
    PositiveRecurrent P := by sorry

end ProcessingNetworks.DTMCFoster
