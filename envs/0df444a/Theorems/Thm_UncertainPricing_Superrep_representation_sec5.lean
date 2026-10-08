-- Prove2me | Theorems.Thm_UncertainPricing_Superrep_representation_sec5
-- name    : UncertainPricing.Superrep.representation_sec5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:50:47.039925+00:00
-- url     : https://prove2.me/theorems/1919050c-9656-4051-8a84-e48e1d77cdad
-- title:
--   §5, p. 19, display before §5.1 — Λ̃(f̃) = sup_{λ∈𝒬} λ(f̃) on C(Ω̃), each λ ∈ 𝒬 a probability Q on Ω̃
-- statement:
--   Let $\mathbf P$ be a set of martingale measures on $\Omega$ satisfying $H(\bar\mu)$, with $\bar\mu$ Hölder continuous, and let $\tilde\Omega$ be the Stone–Čech compactification of $\Omega$. For every bounded continuous $f$ on $\Omega$, with continuous extension $\tilde f$ to $\tilde\Omega$,
--   $$\Lambda(f)=\tilde\Lambda(\tilde f)=\sup_{Q\in\mathcal Q}E_Q\tilde f,$$
--   where $\mathcal Q$ is the set of probability measures $Q$ on $\tilde\Omega$ with $E_Q\tilde g\le\Lambda(g)$ for every $g\in C_b(\Omega)$.
--
--   This dual representation of the superreplication price on bounded continuous claims is the starting point of the proof of Theorem 3.1: every $Q\in\mathcal Q$ is then shown to induce a martingale measure $Q^*$ on $\Omega$ with the bracket bounds.
--
--   **Formalization Note.** The dominated linear forms of the page are represented by their measures; regularity of $Q$ is not imposed (it changes no integral of a continuous function). The supremum is in `EReal`. Hölder continuity of $\bar\mu$ is the standing assumption of §4–§5 (pp. 12, 20).
-- source:
--   Denis & Martini, arXiv:math/0607111v1, §5, display before §5.1, p. 19 (as in §4.2, p. 13)

import Mathlib
import Definitions.Def_UncertainPricing_Superrep_Setting
import Definitions.Def_UncertainPricing_Superrep_Compact

namespace UncertainPricing.Superrep

open MeasureTheory Filter Topology BoundedContinuousFunction

theorem representation_sec5 (T : ℝ) (hT : 0 < T) (μU : StieltjesFunction ℝ) (hμU : IsDistFn T μU)
    (Ps : Set (Measure (Ω T))) (hPs : ∀ P ∈ Ps, IsMartingaleMeasure P ∧ HypU μU P)
    (hHol : IsHolder T μU) (f : Ω T →ᵇ ℝ) :
    Lam Ps μU f = ⨆ Q ∈ Qset Ps μU, ((∫ x, ext f x ∂Q : ℝ) : EReal) := by sorry

end UncertainPricing.Superrep
