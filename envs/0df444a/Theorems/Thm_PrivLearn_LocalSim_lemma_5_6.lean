-- Prove2me | Theorems.Thm_PrivLearn_LocalSim_lemma_5_6
-- name    : PrivLearn.LocalSim.lemma_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:51:02.850096+00:00
-- url     : https://prove2.me/theorems/92eaf345-9c14-4a1d-994f-69d96a53f483
-- title:
--   Lemma 5.6 — A_g approximates E[g] within ±τ with probability ≥ 1 − β from n ≥ c·log(1/β)b²/(ε²τ²) samples
-- statement:
--   There is an absolute constant $c>0$ with the following property. Let $P$ be a probability distribution on a domain $D$, let $g:D\to[-b,b]$ be measurable, and let $b,\varepsilon,\tau>0$, $0<\beta<1$ with $\varepsilon\le1$ and $\varepsilon\tau\le4b$. If the database $z=(z_1,\dots,z_n)$ has
--   $$n\ \ge\ c\cdot\frac{\ln(1/\beta)\,b^2}{\varepsilon^2\tau^2}$$
--   entries drawn i.i.d. from $P$, then the local algorithm $\mathcal A_g(n,\varepsilon,LR_z)$ approximates $\mathbb E_{u\sim P}[g(u)]$ within additive error $\pm\tau$ with probability at least $1-\beta$:
--   $$\Pr_{z\sim P^n,\ \eta\sim\mathrm{Lap}(2b/\varepsilon)^n}\Bigl[\Bigl|\frac1n\sum_{i=1}^n\bigl(g(z_i)+\eta_i\bigr)-\mathbb E_{u\sim P}[g(u)]\Bigr|\le\tau\Bigr]\ \ge\ 1-\beta.$$
--
--   One run of $\mathcal A_g$ thus answers one statistical query; Theorem 5.7 applies it once per query on fresh data.
--
--   **Formalization Note.** "For sufficiently large constant $c$" is stated as $\exists c>0$ before every other quantifier. The paper's $\log$ is base 2; we use the natural logarithm, which only changes $c$. The probability is over the database and the Laplace noises jointly (product measure). Two hypotheses are added because the printed lemma is false without them. (i) $\varepsilon\tau\le4b$: with $g\equiv b$ and $K=\varepsilon\tau/b$ large, $n=1$ is allowed for $\beta=e^{-K^2/c}$ and the error probability $e^{-K/2}$ exceeds $\beta$. (ii) $\varepsilon\le1$: for large $\varepsilon$ the threshold $c\ln(1/\beta)b^2/(\varepsilon^2\tau^2)$ falls below the $\Theta(b^2\ln(1/\beta)/\tau^2)$ samples needed to control the sampling error of $g$ (e.g. $g=\pm b$ fair coin, $\tau\ll b$, $\varepsilon=4b/\tau$); the paper's remark that the sampling bound "is smaller than the lower bound on $n$ in the lemma by a factor of $O(\varepsilon^{-2})$" presumes $\varepsilon=O(1)$. Every use in the paper satisfies both.
-- source:
--   Kasiviswanathan, Lee, Nissim, Raskhodnikova and Smith, What Can We Learn Privately?, arXiv:0803.0924v3, p. 20, Lemma 5.6

import Mathlib
import Definitions.Def_PrivLearn_LocalSim_Privacy
import Definitions.Def_PrivLearn_LocalSim_Simulation

namespace PrivLearn.LocalSim

open MeasureTheory

/-- Lemma 5.6 (p. 20): there is an absolute constant `c > 0` such that if the database
`z = (z_1, …, z_n)` has `n ≥ c · ln(1/β) b² / (ε² τ²)` entries drawn i.i.d. from `P`, then for a
measurable query `g : Dom → [−b, b]` the output of `A_g(n, ε, LR_z)` is within `τ` of
`E_{u∼P}[g(u)]` with probability at least `1 − β` (over the database and the Laplace noises).
Stated for `ε ≤ 1` and in the regime `ε τ ≤ 4 b`, without which it is false. -/
theorem lemma_5_6 :
    ∃ c : ℝ, 0 < c ∧
      ∀ (Dom : Type) [MeasurableSpace Dom] (P : Measure Dom) [IsProbabilityMeasure P]
        (g : Dom → ℝ) (b ε τ β : ℝ) (n : ℕ),
        Measurable g → (∀ u, |g u| ≤ b) →
        0 < b → 0 < ε → ε ≤ 1 → 0 < τ → ε * τ ≤ 4 * b → 0 < β → β < 1 →
        c * Real.log (1 / β) * b ^ 2 / (ε ^ 2 * τ ^ 2) ≤ n →
        ENNReal.ofReal (1 - β) ≤
          ((Measure.pi fun _ : Fin n => P).prod
              (Measure.pi fun _ : Fin n => PrivLearn.Generic.laplace (2 * b / ε)))
            {p | |avgResp g p.1 p.2 - ∫ x, g x ∂P| ≤ τ} := by sorry

end PrivLearn.LocalSim
