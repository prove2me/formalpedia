-- Prove2me | Theorems.Thm_RGGDetect_theorem_1
-- name    : RGGDetect.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:38:47.905345+00:00
-- url     : https://prove2.me/theorems/d71b8ffb-d815-4ccd-966d-3247da66ca18
-- title:
--   Theorem 1 — $\mathrm{KL}(P_{\mathrm{RGG}}\|P_{\mathrm{ER}})=o(1)$ when $p\to0$, $p\ge n^{-1+\delta}$, $d\gg(np\log(1/p))^3$
-- statement:
--   Fix any constant $\delta>0$. Let $P_{\mathrm{RGG}}$ be the law of the hard-threshold spherical random geometric graph on $n$ vertices in dimension $d$ with edge density $p$, and $P_{\mathrm{ER}}$ the law of $G(n,p)$. Suppose that
--
--   $$
--   p\to0,\qquad p\ge n^{-1+\delta},\qquad d\gg\big(np\log(1/p)\big)^3. \tag{1}
--   $$
--
--   Then
--
--   $$
--   \mathrm{KL}(P_{\mathrm{RGG}}\|P_{\mathrm{ER}})=o(1).
--   $$
--
--   This is the impossibility half of the conjecture of Liu, Mohanty, Schramm and Yang: above the threshold $d\asymp(np\log(1/p))^3$ the geometry cannot be detected from the graph, throughout the sparse regime with polynomially growing average degree.
--
--   **Formalization Note** $p,d,\tau$ are sequences in $n$. $d\gg f$ is written as "for every $\varepsilon>0$, eventually $f\le\varepsilon d$", the meaning fixed by (2). The threshold $\tau_n$ is any sequence solving $\mathbb P\{\langle x_1,x_2\rangle\ge\tau_n\}=p_n$ for large $n$. The laws are finite sums of point masses on the graphs on $[n]$, and KL is Mathlib's `klDiv` with values in $[0,\infty]$.
--
--   Differences from the source:
--   - generalization: the hypotheses (1) for all n → each hypothesis only for all large n; reason: the conclusion is a limit, so sequences satisfying (1) for all n are covered
--   - generalization: τ = τ(d, p) chosen so that P{⟨x₁, x₂⟩ ≥ τ} = p → any sequence τ_n with P{⟨x₁, x₂⟩ ≥ τ_n} = p_n for all large n; reason: for d ≥ 2 and 0 < p < 1 the solution is unique (⟨x₁, x₂⟩ has a positive density on (−1, 1)), so the paper's τ(d, p) is covered
--   - encoding: d ≫ (np log(1/p))³ → for every ε > 0, eventually (np log(1/p))³ ≤ ε·d; reason: the meaning fixed by (2), ε_n = (npL)³/d = o(1); a quotient form would hold at d = 0 in Lean
--   - encoding: the laws P_RGG, P_ER and KL → finite sums of point masses on SimpleGraph (Fin n); Mathlib's klDiv in [0, ∞]; reason: the same laws on the finite set of graphs
-- source:
--   Du, Mao, Sun, Wu, Xu, Sharp detection thresholds for random geometric graphs with polynomial average degrees, arXiv:2610.08517 (held version, sha256 e7bebd4a…), Theorem 1, eq. (1), p.1 (PDF p.3)

import Mathlib
import Definitions.Def_RGGDetect_rggLaw
import Definitions.Def_RGGDetect_erLaw

open Filter Topology

namespace RGGDetect

/-- **Theorem 1** (Du, Mao, Sun, Wu, Xu, *Sharp detection thresholds for random geometric graphs with
polynomial average degrees*, arXiv:2610.08517 (held version, sha256 e7bebd4a…), Theorem 1, p.1,
eq. (1)): fix any constant `δ > 0`. Suppose that `p → 0`, `p ≥ n^{-1+δ}`, `d ≫ (np log(1/p))³`.
Then `KL(P_RGG∥P_ER) = o(1)`.

**Formalization Note** The edge density `p`, the dimension `d` and the threshold `τ` are sequences in
the number of vertices `n`. `d ≫ f` is written as "for every `ε > 0`, eventually `f ≤ ε d`" (the
paper's `ε_n = (npL)³/d = o(1)`, (2)), never as a quotient. The hypotheses are required for all large
`n`; `τ` is any sequence that eventually solves the cap equation `P{⟨x₁, x₂⟩ ≥ τ} = p`, which for
`d ≥ 2` and `0 < p < 1` is the paper's `τ(d, p)`. The laws are finite sums of point masses on the
graphs on `Fin n`; `KL` is Mathlib's `klDiv` with values in `[0, ∞]`. -/
theorem theorem_1 (δ : ℝ) (hδ : 0 < δ) (p : ℕ → ℝ) (d : ℕ → ℕ) (τ : ℕ → ℝ)
    (hp0 : Tendsto p atTop (𝓝 0))
    (hpl : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (-1 + δ) ≤ p n)
    (hd : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ((n : ℝ) * p n * Real.log (1 / p n)) ^ 3 ≤ ε * d n)
    (hτ : ∀ᶠ n : ℕ in atTop, capProb (d n) (τ n) = p n) :
    Tendsto (fun n => InformationTheory.klDiv (rggLaw n (d n) (τ n)) (erLaw n (p n)))
      atTop (𝓝 0) := by sorry

end RGGDetect
