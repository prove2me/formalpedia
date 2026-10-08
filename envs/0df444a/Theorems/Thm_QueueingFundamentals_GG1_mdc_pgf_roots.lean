-- Prove2me | Theorems.Thm_QueueingFundamentals_GG1_mdc_pgf_roots
-- name    : QueueingFundamentals.GG1.mdc_pgf_roots
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T19:49:14.67693+00:00
-- url     : https://prove2.me/theorems/007984b6-ca7a-4aaf-8fd9-c27ff3fa0b7f
-- title:
--   Eqs. (6.19)–(6.20) — the M/D/c generating function via the roots of z^c = e^{−λ(1−z)}
-- statement:
--   Consider the M/D/c queue with $c\ge1$ servers, unit service time, Poisson arrivals at rate $\lambda$, and $0<\lambda<c$. Let $z_1,\dots,z_{c-1}$ be distinct complex numbers with $|z_i|\le1$ and $z_i\ne1$ such that $1,z_1,\dots,z_{c-1}$ are all the roots of
--
--   $$
--   z^c=e^{-\lambda(1-z)}
--   $$
--
--   in the closed unit disk. Then every steady-state distribution $(p_n)$ of (6.17), with generating function $P(z)$, satisfies for $|z|\le1$
--
--   $$
--   P(z)=\frac{\lambda-c}{(1-z_1)\cdots(1-z_{c-1})}\cdot\frac{(z-1)(z-z_1)\cdots(z-z_{c-1})}{1-z^ce^{\lambda(1-z)}}, \tag{6.19}
--   $$
--
--   and, for $c\ge2$,
--
--   $$
--   p_0=\frac{(c-\lambda)(-1)^{c-1}\prod_{i=1}^{c-1}z_i}{\prod_{i=1}^{c-1}(1-z_i)}. \tag{6.20}
--   $$
--
--   These formulas remove the $c$ unknown probabilities from (6.18); the remaining $p_1,\dots,p_{c-1}$ follow from a linear system and $p_c,p_{c+1},\dots$ from (6.17).
--
--   **Formalization Note** (6.19) is stated with the denominator cleared, on the closed unit disk. The roots are given as an injective family indexed by $\{1,\dots,c-1\}$ that exhausts the roots other than $1$; that such a family exists (exactly $c-1$ distinct roots besides $1$) is what the book obtains from Rouché's theorem and Problem 6.10, so it is a hypothesis here rather than a conclusion.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, pp.295–296, Eqs. (6.19) and (6.20), with the roots of z^c = e^{−λ(1−z)} on p.296

import Mathlib
import Definitions.Def_QueueingFundamentals_GG1_MDc

namespace QueueingFundamentals.GG1

/-- Eqs. (6.19)–(6.20) (p.296) for the M/D/c queue with `λ < c`. Let `1, z_1, …, z_{c−1}` be the
roots of `z^c = e^{−λ(1−z)}` in `|z| ≤ 1` (given as `c − 1` distinct points `z_i ≠ 1` that exhaust the
roots other than `1`). Then every steady-state distribution `p` of (6.17) has
`P(z) = ((λ − c)/((1 − z_1)⋯(1 − z_{c−1}))) · ((z − 1)(z − z_1)⋯(z − z_{c−1}))/(1 − z^c e^{λ(1−z)})`
for `|z| ≤ 1` (6.19, stated with the denominator cleared), and, for `c ≥ 2`,
`p_0 = (c − λ)(−1)^{c−1} ∏ z_i / ∏ (1 − z_i)` (6.20). -/
theorem mdc_pgf_roots (lam : ℝ) (hlam : 0 < lam) (c : ℕ) (hc : 1 ≤ c) (hstab : lam < c)
    (z : Fin (c - 1) → ℂ) (hinj : Function.Injective z)
    (hroot : ∀ i, ‖z i‖ ≤ 1 ∧ z i ≠ 1 ∧ z i ^ c = Complex.exp (-(lam : ℂ) * (1 - z i)))
    (hall : ∀ w : ℂ, ‖w‖ ≤ 1 → w ≠ 1 → w ^ c = Complex.exp (-(lam : ℂ) * (1 - w)) →
      ∃ i, z i = w)
    (p : ℕ → ℝ) (hp : IsMDcStationary lam c p) :
    (∀ w : ℂ, ‖w‖ ≤ 1 →
      QueueingFundamentals.MG1.pgf p w * (1 - w ^ c * Complex.exp ((lam : ℂ) * (1 - w))) =
        ((lam : ℂ) - c) / (∏ i, (1 - z i)) * ((w - 1) * ∏ i, (w - z i))) ∧
    (2 ≤ c →
      (p 0 : ℂ) = ((c : ℂ) - lam) * (-1) ^ (c - 1) * (∏ i, z i) / ∏ i, (1 - z i)) := by sorry

end QueueingFundamentals.GG1
