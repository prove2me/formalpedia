-- Prove2me | Theorems.Thm_QMomentMatch_FirstBound_lemma_3_7
-- name    : QMomentMatch.FirstBound.lemma_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T18:59:41.360385+00:00
-- url     : https://prove2.me/theorems/cd4f8c0d-6a92-4305-9e5b-6180979ccc4c
-- title:
--   Lemma 3.7 — continuous hybrid argument
-- statement:
--   Fix integers $A,m\ge1$ and let $S=\{0\}\cup[A]$. Let $h:S^m\to[0,1]$ be invariant under permutations of its coordinates and put $q_w(s)=h(w,s)$ for $w\in S^{m-1}$, $s\in S$. Let $(\pi_u)_{0\le u\le1}$ be a continuous, piecewise $C^1$ path of probability distributions on $S$, and $F(u)=\mathbb E_{\pi_u^{\otimes m}}[h]$. At every differentiability point $u$ of the path, with $\dot\pi_u(s)=\frac{d}{du}\pi_u(s)$,
--   $$F'(u)=m\,\mathbb E_{w\sim\pi_u^{\otimes(m-1)}}\Big[\sum_{s\in S}\dot\pi_u(s)q_w(s)\Big].\tag{13}$$
--   Consequently,
--   $$|F(1)-F(0)|\le m\int_0^1\mathbb E_{w\sim\pi_u^{\otimes(m-1)}}\Big[\Big|\sum_{s\in S}\dot\pi_u(s)q_w(s)\Big|\Big]\,du.\tag{14}$$
--
--   This continuous form of the hybrid argument reduces the comparison of two product laws to a one-coordinate computation along a path joining them.
--
--   **Formalization Note** (13) is stated at every $u\in[0,1]$ at which every coordinate $v\mapsto\pi_v(s)$ has a derivative $\pi'(s)$ relative to $[0,1]$ (one-sided at $u=0,1$), as a derivative of $F$ relative to $[0,1]$. In (14), $\dot\pi_u(s)$ is Lean's `deriv`, which can differ from the one-sided derivatives only at the finitely many breakpoints of the path, a null set for the integral.
--
--   Differences from the source:
--   - encoding: $S^{m-1}$ and $(w,s)$ → `Fin (m - 1) → S` and `appendLast w s` (the coordinate $s$ in last position); reason: the source moves the chosen coordinate to the last position (p. 18).
--   - reading: "at every differentiability point of the path" → at every $u\in[0,1]$ where each coordinate has a derivative within $[0,1]$ (one-sided at the endpoints); reason: the path is only defined on $[0,1]$, so differentiability there is relative to $[0,1]$.
--   - encoding: "continuous, piecewise $C^1$" → coordinates continuous on $[0,1]$ and $C^1$ on each closed piece of a finite partition $0=t_0<\dots<t_k=1$; reason: the standard meaning, made explicit; it makes the integrand in (14) integrable.
--   - encoding: $\dot\pi_u$ in (14) → `deriv`; reason: it agrees with the derivative off the finitely many breakpoints, which do not change the integral.
--   - encoding: distributions on S = {0} ∪ [A] → real probability vectors on Fin (A + 1); reason: finite laws and expectations are represented by the same masses and finite sums.
-- source:
--   Chandrima Kayal, Frédéric Magniez, Sayantan Sen, Dániel Szabó, STOC 2027 submission #564 (October 2026), §3.2 standing setting and Lemma 3.7, p. 18

import Mathlib
import Definitions.Def_QMomentMatch_FirstBound_Basic

namespace QMomentMatch.FirstBound

/-- Lemma 3.7 (Continuous hybrid argument), p. 18, in the standing setting of §3.2 (integers
`A, m ≥ 1`, `S = {0} ∪ [A]`). Part (13) is stated at every `u ∈ [0,1]` where every coordinate of
the path has a derivative (one-sided at the ends); part (14) uses `π̇_u(s) = d/du π_u(s)`. -/
theorem lemma_3_7 (A m : ℕ) (hA : 1 ≤ A) (hm : 1 ≤ m)
    (h : (Fin m → Fin (A + 1)) → ℝ) (h01 : ∀ z, h z ∈ Set.Icc (0 : ℝ) 1)
    (hsymm : ∀ (σ : Equiv.Perm (Fin m)) (z : Fin m → Fin (A + 1)), h (z ∘ σ) = h z)
    (π : ℝ → Fin (A + 1) → ℝ) (hπ : IsPiecewiseC1ProbPath π) :
    (∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ π' : Fin (A + 1) → ℝ,
      (∀ s, HasDerivWithinAt (fun v => π v s) (π' s) (Set.Icc 0 1) u) →
        HasDerivWithinAt (fun v => prodExp (π v) h)
          ((m : ℝ) * prodExp (π u) fun w : Fin (m - 1) → Fin (A + 1) =>
            ∑ s, π' s * h (appendLast w s))
          (Set.Icc 0 1) u) ∧
    |prodExp (π 1) h - prodExp (π 0) h| ≤
      (m : ℝ) * ∫ u in (0 : ℝ)..1, prodExp (π u) fun w : Fin (m - 1) → Fin (A + 1) =>
        |∑ s, deriv (fun v => π v s) u * h (appendLast w s)| := by sorry

end QMomentMatch.FirstBound
