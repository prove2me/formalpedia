-- Prove2me | Theorems.Thm_SingularStopperVI_lemma_5_7
-- name    : SingularStopperVI.lemma_5_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:40:37.451987+00:00
-- url     : https://prove2.me/theorems/98e79b1c-34e1-4fb4-b568-cf2775fffc8c
-- title:
--   Lemma 5.7: upper bound on the time derivative of $u^{\varepsilon,\delta}$
-- statement:
--   Throughout, $b,\sigma$ satisfy Assumption 3.1, $f,g,h$ satisfy Assumption 3.2, $T>0$, $r\ge0$, and $(\Omega,\mathcal F,\mathbb F,\mathsf P,W)$ is the stochastic basis of §3. The penalties $(\psi_\varepsilon)$ of p.8 are fixed.
--
--   Let $K_4=K_0(1+T)+K_2$, with $K_0$, $K_2$ from Assumption 3.2. Every solution $u$ of Problem C with $\varepsilon,\delta\in(0,1)$ satisfies, for $0\le t_1<t_2\le T$ and all $x$,
--
--   $$
--   u(t_2,x)-u(t_1,x)\le K_4(t_2-t_1),
--   $$
--
--   and $\partial_tu(t,x)\le K_4$ for $t<T$. Hence (5.28) holds at $t=T$ too, wherever the limit defining $\partial_tu(T,x)$ on p.26 exists.
--
--   The estimate gives the one-sided control of $\partial_t u$ that is used in the bound on the gradient penalty.
--
--   Differences from the source:
--   - encoding: the stochastic basis is fixed at the start of §3 → a universally quantified basis `B` with `B.IsValid`, also where the conclusion does not mention it; reason: it is the paper's standing setting, and the proof is probabilistic
--   - encoding: "for some $\alpha$", "there is $K_0$, $K_1$, $K_2$" in Assumption 3.2, and the derivatives of $g$ → $\alpha$, $K_0$, $K_1$, $K_2$ and $J_g$ are parameters of `Assumption32`; reason: universally quantifying over the data of a hypothesis is the same as assuming that they exist; Lemmas 5.6 and 5.7 name these constants
--   - encoding: bounded sets $\mathcal O\subset\mathbb R^{d+1}_{0,T}$ and $B\subset\mathbb R^d$ → the cylinders $[0,T]\times\bar B_R$ and the balls $\bar B_R$; reason: they exhaust the bounded sets, and the classes are monotone in the set
--   - reading: "$\mathbb F$-adapted Brownian motion" (p.5) → an $\mathbb F$-Brownian motion: increments after $s$ are independent of $\mathcal F_s$; reason: the Itô integral in (3.1) is not defined otherwise
--   - reading: (3.7) prints "all $x\in\mathbb R^{d+1}_{0,T}$" → $x\in\mathbb R^d$; reason: $h(t,x)$ and $g(t,x)$ take $x\in\mathbb R^d$; a slip of the page
--   - encoding: the family $(\psi_\varepsilon)$ is fixed once → $\psi$ is universally quantified, before the constants; reason: the constants may depend on it and not on $\varepsilon,\delta$
--   - generalization: "$\partial_tu\le K_4$ on $\mathbb R^{d+1}_{0,T}$, with $K_4$ depending only on $K_0$, $K_2$", the derivative at $T$ being a limit → the one-sided Lipschitz bound on $[0,T]$ with the explicit $K_4=K_0(1+T)+K_2$ of the proof, and $\partial_tu\le K_4$ on $[0,T)$; reason: it implies (5.28) wherever the derivative exists, without assuming that the limit at $T$ exists; $K_4$ depends on $T$ as well, which is fixed
-- source:
--   Bovo, De Angelis, Issoglio, arXiv:2203.06247v3, Lemma 5.7, (5.28), p.26

import Mathlib
import Definitions.Def_SingularStopperVI_Penalised

open MeasureTheory Set
open scoped ENNReal NNReal

namespace SingularStopperVI

/-- Bovo, De Angelis, Issoglio, arXiv:2203.06247v3, Lemma 5.7, (5.28), p.26, with the constant `K₄ = K₀(1+T) + K₂` of its proof.
For `0 ≤ t₁ < t₂ ≤ T`, `u(t₂,x) − u(t₁,x) ≤ K₄(t₂−t₁)`; hence `∂_t u ≤ K₄` on `[0,T)`, and at `T` wherever the
limit that defines `∂_t u(T,x)` on p.26 exists. -/
theorem lemma_5_7 {Ω : Type*} [MeasurableSpace Ω] {d d' : ℕ} (B : Basis d' Ω) (hB : B.IsValid)
    (D : Data d d') (hD : D.Standing) (h31 : Assumption31 D) {α K0 K1 K2 : ℝ} {Jg : Jet d}
    (h32 : Assumption32 D α Jg K0 K1 K2)
    {ψ : ℝ → ℝ → ℝ} (hψ : IsPenalty ψ) :
    ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ δ ∈ Ioo (0 : ℝ) 1, ∀ u K, IsProblemC D ψ α ε δ u K →
      (∀ t₁ t₂ x, 0 ≤ t₁ → t₁ < t₂ → t₂ ≤ D.T →
        u t₂ x - u t₁ x ≤ (K0 * (1 + D.T) + K2) * (t₂ - t₁)) ∧
      ∀ t ∈ Ico 0 D.T, ∀ x, K.ut t x ≤ K0 * (1 + D.T) + K2 := by sorry

end SingularStopperVI
