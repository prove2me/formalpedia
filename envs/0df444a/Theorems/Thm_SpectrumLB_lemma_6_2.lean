-- Prove2me | Theorems.Thm_SpectrumLB_lemma_6_2
-- name    : SpectrumLB.lemma_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:36:40.762971+00:00
-- url     : https://prove2.me/theorems/5353d9c8-c61c-49d1-bcf1-65ab22ac7913
-- title:
--   Lemma 6.2 — triangular discrimination $\le C(\mathrm{bad}(G)+\mathrm{dev}_{\lambda,G})$
-- statement:
--   There is an absolute constant $C>0$ with the following property. Let $p=(p_y)$, $q=(q_y)$ be probability distributions on a finite set $\Omega$, and set
--
--   $$
--   \mu_y=\frac{p_y+q_y}2,\qquad \xi_y=\frac{q_y-p_y}{q_y+p_y}\quad(\xi_y=0\text{ if }p_y=q_y=0).
--   $$
--
--   Let $G\subseteq\Omega$ be a set on which $p_y,q_y>0$, let $\lambda\in\mathbb R$, and define $\mathrm{bad}(G)=\mu(G^c)$ and $\mathrm{dev}_{\lambda,G}=\mathbf E_\mu\big[(\log(q_y/p_y)-\lambda)^2\mathbf 1_G\big]$. Then
--
--   $$
--   \mathbf E_\mu\,\xi^2\ \le\ C\big(\mathrm{bad}(G)+\mathrm{dev}_{\lambda,G}\big).
--   $$
--
--   The left side is the triangular discrimination between $p$ and $q$, equivalent to the squared Hellinger distance; the lemma bounds it by the deviation of the log-likelihood ratio from a constant, which is how the trace-distance bound of Theorem 5.7 is reduced to moment estimates.
--
--   Differences from the source:
--   - encoding: absolute constant C > 0 → ∃ C > 0 chosen before Ω, p, q, G, λ; reason: meaning of "absolute"
--   - encoding: E_μ and μ(G^c) → finite sums Σ_y μ_y(·) over Ω and over the complement of G; reason: same quantities on a finite set
-- source:
--   Fanizza, O'Donnell, Wadhwa, Spectrum Estimation is Almost as Hard as Tomography, arXiv:2607.29680, Definition 6.1, Eqs. (6.1)–(6.2), and Lemma 6.2, Eqs. (6.4)–(6.5), p. 23

import Mathlib

open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder

namespace SpectrumLB

/-- **Lemma 6.2 (triangular discrimination via the log-likelihood).**
Fanizza, O'Donnell, Wadhwa, *Spectrum Estimation is Almost as Hard as Tomography*, arXiv:2607.29680, Definition 6.1, Eqs. (6.1)–(6.2), and Lemma 6.2, Eqs. (6.4)–(6.5), p. 23: "Let G ⊆ Ω be a set on
which p_y, q_y > 0. Fix some λ ∈ R, and define bad(G) := μ(G^c), dev_{λ,G} := E_μ[(log(q_y/p_y) − λ)^2 1_G].
Then, E_μ ξ^2 ≤ C(bad(G) + dev_{λ,G}), for some absolute constant C > 0."

Here `p, q` are probability vectors on a finite set `Ω`, `μ_y = (p_y + q_y)/2` and
`ξ_y = (q_y − p_y)/(q_y + p_y)` (with `ξ_y = 0` when `p_y = q_y = 0`).

**Formalization Note.** "Absolute" is `∃ C` before `Ω, p, q, G, λ`. Lean's `x / 0 = 0` gives exactly the
convention `ξ_y = 0` when `p_y = q_y = 0`. Expectations under `μ` are written as finite sums. -/
theorem lemma_6_2 :
    ∃ C : ℝ, 0 < C ∧ ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω] (p q : Ω → ℝ),
      (∀ y, 0 ≤ p y) → (∀ y, 0 ≤ q y) → ∑ y, p y = 1 → ∑ y, q y = 1 →
      ∀ G : Finset Ω, (∀ y ∈ G, 0 < p y ∧ 0 < q y) → ∀ lam : ℝ,
        ∑ y, (p y + q y) / 2 * ((q y - p y) / (q y + p y)) ^ 2 ≤
          C * (∑ y ∈ Gᶜ, (p y + q y) / 2 +
            ∑ y ∈ G, (p y + q y) / 2 * (Real.log (q y / p y) - lam) ^ 2) := by sorry

end SpectrumLB
