-- Prove2me | Theorems.Thm_RobustSAA_Convergence_proposition_8
-- name    : RobustSAA.Convergence.proposition_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:17:20.263734+00:00
-- url     : https://prove2.me/theorems/87ca9afc-cd89-4f67-9011-ee513799487d
-- title:
--   Proposition 8, p. 36 — uniform consistency and Assumptions 1, 3 give E_{F_N}[c(x;ξ)] → E_F[c(x;ξ)] a.s. along every F_N ∈ 𝓕_N
-- statement:
--   Let $\Xi\subseteq\mathbb R^d$ be closed, let $N\mapsto\mathcal F_N$ be the confidence region of a uniformly consistent test, and let the data $\xi^1,\xi^2,\dots$ be i.i.d. from $F$. Let $X$ and the cost $c(x;\xi)$ satisfy the standing assumptions of §1.2 and Assumptions 1 and 3. Then, almost surely, for every $x\in X$ and every sequence of distributions $F_N$ with $F_N\in\mathcal F_N$ for all large $N$,
--   $$\mathbb E_{F_N}[c(x;\xi)]\longrightarrow\mathbb E_F[c(x;\xi)]\qquad(N\to\infty).$$
--
--   This is the first step of the proof of Theorem 2: it turns uniform consistency, a statement about weak convergence, into convergence of the expected costs of every distribution the DUS can retain. In particular a single null set serves all $x$ and all sequences.
--
--   **Formalization Note** $\mathbb E_{F_N}$ is the extended-real expectation, equal to $+\infty$ when $c(x;\cdot)$ is not $F_N$-integrable, so the conclusion includes that $c(x;\cdot)$ is eventually $F_N$-integrable. "Sequences $F_N\in\mathcal F_N$" is read as membership for all large $N$. Assumption 1 is a hypothesis as on the page, although the paper's proof does not use it.
-- source:
--   Bertsimas, Gupta, Kallus, Robust Sample Average Approximation, arXiv:1408.4445v3, Proposition 8, §10.5, p. 36

import Mathlib
import Definitions.Def_RobustSAA_Convergence_Setting

open MeasureTheory Filter Topology

namespace RobustSAA.Convergence

theorem proposition_8 {d dx : ℕ} {Ξ : Set (Pt d)} (hΞ : IsClosed Ξ) (𝓕 : DUS Ξ)
    (h𝓕 : IsUniformlyConsistent 𝓕) (F : ProbabilityMeasure ↥Ξ) (X : Set (Pt dx))
    (c : Pt dx → ↥Ξ → ℝ) (hS : Standing F X c) (hA1 : Assumption1 X c)
    (hA3 : Assumption3 F 𝓕 X c) :
    ∀ᵐ ω ∂(dataLaw F), ∀ x ∈ X, ∀ G : ℕ → ProbabilityMeasure ↥Ξ,
      (∀ᶠ N in atTop, G N ∈ 𝓕 N (sample ω N)) →
        Tendsto (fun N => expect (G N) (c x)) atTop (𝓝 ((trueObj F c x : ℝ) : EReal)) := by sorry

end RobustSAA.Convergence
