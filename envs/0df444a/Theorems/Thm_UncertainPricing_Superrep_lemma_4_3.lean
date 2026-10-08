-- Prove2me | Theorems.Thm_UncertainPricing_Superrep_lemma_4_3
-- name    : UncertainPricing.Superrep.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:49:46.664253+00:00
-- url     : https://prove2.me/theorems/c2c625f7-cfb1-44df-ab49-69441b2c4906
-- title:
--   Lemma 4.3, p. 13 — Λ̃²(f̃g̃) ≤ Λ̃(f̃²) Λ̃(g̃²), read on C_b(Ω)
-- statement:
--   Let $\mathbf P$ be a set of martingale measures on $\Omega$ satisfying $H(\bar\mu)$, with $\bar\mu$ Hölder continuous. For bounded continuous $f,g$ on $\Omega$,
--   $$\Lambda(fg)^2\le\Lambda(f^2)\,\Lambda(g^2).$$
--   Since $\tilde f\tilde g=(fg)^\sim$ and $\tilde\Lambda(\tilde h)=\Lambda(h)$, this is the page's inequality $\tilde\Lambda^2(\tilde f\tilde g)\le\tilde\Lambda(\tilde f^2)\tilde\Lambda(\tilde g^2)$ for $\tilde f,\tilde g\in C(\tilde\Omega)$.
--
--   This Cauchy–Schwarz inequality for the sublinear price is used to control $\Lambda(f\{S^n-(\langle B\rangle_t-\langle B\rangle_s)\})$ when the bracket bounds are transferred to $Q\in\mathcal Q$.
--
--   **Formalization Note.** The statement is written on $C_b(\Omega)$, which is in bijection with $C(\tilde\Omega)$ by $f\mapsto\tilde f$, so it needs no compactification. Products are in `EReal` ($\Lambda\equiv-\infty$ when $\mathbf P=\emptyset$, and then both sides are $+\infty$). The page is in §4 (bounded paths); the inequality is read on the full $\Omega$ of §5, whose standing assumption (Hölder $\bar\mu$, p. 20) is kept.
-- source:
--   Denis & Martini, arXiv:math/0607111v1, Lemma 4.3, p. 13

import Mathlib
import Definitions.Def_UncertainPricing_Superrep_Setting

namespace UncertainPricing.Superrep

open MeasureTheory Filter Topology BoundedContinuousFunction

theorem lemma_4_3 (T : ℝ) (hT : 0 < T) (μU : StieltjesFunction ℝ) (hμU : IsDistFn T μU)
    (Ps : Set (Measure (Ω T))) (hPs : ∀ P ∈ Ps, IsMartingaleMeasure P ∧ HypU μU P)
    (hHol : IsHolder T μU) (f g : Ω T →ᵇ ℝ) :
    Lam Ps μU (fun ω => f ω * g ω) * Lam Ps μU (fun ω => f ω * g ω) ≤
      Lam Ps μU (fun ω => f ω ^ 2) * Lam Ps μU (fun ω => g ω ^ 2) := by sorry

end UncertainPricing.Superrep
