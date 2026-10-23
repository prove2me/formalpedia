-- Prove2me | Theorems.Thm_TimeDepFolk_Asymptotic_lemma_4_4
-- name    : TimeDepFolk.Asymptotic.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:19:16.511505+00:00
-- url     : https://prove2.me/theorems/f72b61c5-dc40-46f6-a071-f4fb4bb5cf3e
-- title:
--   Lemma 4.4, p. 16 — for patient θ^k and k ≥ K(η), x = Σ_m θ^k_m x′_{φ(m)} with each x′ chosen among perturbed vertices
-- statement:
--   Let $(\theta^k)_{k\ge1}$ be a sequence of patient evaluations, and let $x$ be a convex combination of vectors $x_1,\dots,x_L\in\mathbb R^I$ with $L\le|I|+1$, such that for every $\ell$ the vectors $\{x_{\ell'}-x_\ell:\ell'\ne\ell\}$ are linearly independent. Let $\eta>0$ with $B_\eta(x)\subseteq\operatorname{co}\{x_\ell\}$ and put $\eta'=\eta/5$. Then there is $K(\eta)$ such that for every $k\ge K(\eta)$ the following holds: for any family of vectors $\{x_{\ell,m}:1\le\ell\le L,\ m\ge1\}$ with each $x_{\ell,m}\in B_{\eta'}(x_\ell)$, there is a sequence of indices $(\varphi(m))_{m\ge1}$ such that
--   $$\sum_{m=1}^{\infty}\theta^k_m\,x_{\varphi(m),m}=x .$$
--
--   This is a perturbed form of Sorin's decomposition of a feasible payoff into a discounted sum of extreme points; the perturbations are what make it usable when the "vertices" are themselves block averages of pure action payoffs.
--
--   **Formalization Note.** Stage $m$ is 0-based. The page says that each $x'_{\varphi(m)}$ takes a value "in $\{x_{\ell,\varphi(m)}:1\le\ell\le L\}$"; the proof (pp. 35 and 37: "each $x'_{\varphi(m)}=x_{\varphi(m),m}$") chooses it at step $m$ from $\{x_{\ell,m}:1\le\ell\le L\}$, so the printed index is a slip and the statement follows the proof: the $m$-th term is `xx (φ m) m`. $K$ depends only on the data $(x_\ell)$, $x$ and $\eta$, not on the perturbations. "Any small $\eta>0$" is read as any $\eta>0$ with the ball condition. The series converges in the sup norm (`HasSum`).
-- source:
--   X. Li, The folk theorem for repeated games with time-dependent discounting, SSRN Working Paper 3407197 (version of August 16, 2019), p. 16, Lemma 4.4 (proof §7.1, pp. 33–35)

import Mathlib
import Definitions.Def_TimeDepFolk_Asymptotic_Model

namespace TimeDepFolk.Asymptotic

theorem lemma_4_4 {ι : Type*} [Fintype ι] (θ : ℕ → Evaluation) (hθ : IsPatient θ)
    {L : ℕ} (hL : L ≤ Fintype.card ι + 1) (x : Fin L → ι → ℝ) (hx : AffineIndependent ℝ x)
    (x0 : ι → ℝ) (hx0 : x0 ∈ convexHull ℝ (Set.range x))
    (η : ℝ) (hη : 0 < η) (hball : Metric.closedBall x0 η ⊆ convexHull ℝ (Set.range x)) :
    ∃ K : ℕ, ∀ k ≥ K, ∀ xx : Fin L → ℕ → ι → ℝ,
      (∀ ℓ m, xx ℓ m ∈ Metric.closedBall (x ℓ) (η / 5)) →
        ∃ φ : ℕ → Fin L, HasSum (fun m => (θ k).θ m • xx (φ m) m) x0 := by sorry

end TimeDepFolk.Asymptotic
