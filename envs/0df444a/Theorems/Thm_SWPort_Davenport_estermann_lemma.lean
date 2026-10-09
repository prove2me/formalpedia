-- Prove2me | Theorems.Thm_SWPort_Davenport_estermann_lemma
-- name    : SWPort.Davenport.estermann_lemma
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T19:22:10.358239+00:00
-- url     : https://prove2.me/theorems/bbb62472-59c4-4f1e-97ca-7950d67a56d7
-- title:
--   Estermann's lemma: $f(1) \ge \tfrac14(1-\sigma)M^{-3(1-\sigma)}$ when $\zeta f$ has nonnegative coefficients (ported to Mathlib 0df444a)
-- statement:
--   **Estermann's lemma** (Montgomery–Vaughan, Lemma 11.13). Suppose that $f(s)$ is analytic for $|s-2| \le 3/2$ and that $|f(s)| \le M$ for $s$ in this disc, where $M \ge 1$. Suppose also that
--   $$
--   F(s) = \zeta(s)f(s) = \sum_{n=1}^{\infty} r(n)\,n^{-s} \qquad (\sigma > 1),
--   $$
--   the Dirichlet series being absolutely convergent for $\sigma > 1$, that $r(1) = 1$, and that $r(n) \ge 0$ for all $n$. If there is a $\sigma \in [19/20, 1)$ such that $f(\sigma) \ge 0$, then
--   $$
--   f(1) \;\ge\; \tfrac14\,(1-\sigma)\,M^{-3(1-\sigma)} .
--   $$
--
--   This is the analytic heart of Siegel's theorem. Applied with $f(s) = L(s,\chi)$ (when no real character has a real zero near $1$) or with $f(s) = L(s,\chi)L(s,\chi_1)L(s,\chi\chi_1)$ evaluated at a real zero $\beta_1$ of $L(s,\chi_1)$, it produces the lower bound $L(1,\chi) \gg_\varepsilon q^{-\varepsilon}$; the ineffectivity of Siegel's constant comes entirely from the choice of $\chi_1$, not from this lemma.
--
--   **Formalization Note.** The conditions "$f(\sigma) \ge 0$" and the conclusion are stated for the real part of $f$ (in the applications $f$ is real on the real axis). The normalization $M \ge 1$ is harmless (replace $M$ by $\max(M,1)$) and is made explicit here; the Dirichlet series is Mathlib's `LSeries`, so its absolute convergence for $\operatorname{Re} s > 1$ is listed as a hypothesis, and $M^{-3(1-\sigma)}$ is the real power.
--
--   **Provenance.** This statement is the prove2.me theorem `Davenport.estermann_lemma` (478fdf36-d856-42b6-a465-a4a0d385c671, statement by alya), published in the Mathlib c5ea003 (Lean 4.30.0) environment, here re-published unchanged in substance under the `SWPort` namespace for the Mathlib 0df444a environment. Its proof is a port of the accepted submission c69ce056-e988-46e0-bf72-1469a42d6e88 by alya, carved so that each piece fits the verifier. The port serves the Siegel–Walfisz theorem used by OpenAI's *Primitive roots for every admissible integer base* (2026), published as `ArtinPrimitiveRoots.siegel_walfisz`. The text above is the original author's natural-language statement.
-- source:
--   prove2.me user alya's proof of the Siegel–Walfisz theorem, Davenport.siegel_walfisz_ap (ff9f3207-eba1-492e-9691-e50480292b68, Mathlib c5ea003), following H. Davenport, Multiplicative Number Theory; ported to Mathlib 0df444a; original statement Davenport.estermann_lemma (478fdf36-d856-42b6-a465-a4a0d385c671) by alya

import Mathlib
import Batteries.Tactic.Lemma

section

namespace SWPort

open Finset DirichletCharacter

open Topology
open scoped ComplexOrder

theorem _root_.SWPort.Davenport.estermann_lemma (f : ℂ → ℂ) (M : ℝ) (r : ℕ → ℝ) (hM : 1 ≤ M)
    (hf : DifferentiableOn ℂ f (Metric.closedBall (2 : ℂ) (3 / 2)))
    (hfM : ∀ s ∈ Metric.closedBall (2 : ℂ) (3 / 2), ‖f s‖ ≤ M)
    (hsum : ∀ s : ℂ, 1 < s.re → LSeriesSummable (fun n => (r n : ℂ)) s)
    (hF : ∀ s : ℂ, 1 < s.re → riemannZeta s * f s = LSeries (fun n => (r n : ℂ)) s)
    (hr₁ : r 1 = 1) (hr : ∀ n, 0 ≤ r n)
    (σ : ℝ) (hσ : 19 / 20 ≤ σ) (hσ₁ : σ < 1) (hfσ : 0 ≤ (f σ).re) :
    (1 / 4) * (1 - σ) * M ^ (-(3 * (1 - σ))) ≤ (f 1).re := by
  sorry

end SWPort
end
