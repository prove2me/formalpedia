-- Prove2me | Theorems.Thm_QMomentMatch_FirstBound_lemma_3_8
-- name    : QMomentMatch.FirstBound.lemma_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T18:59:51.374348+00:00
-- url     : https://prove2.me/theorems/fed8fd88-69cb-4035-a545-8a6217b270bb
-- title:
--   Lemma 3.8 — comparison bound under constant moments, with an exceptional set
-- statement:
--   Fix integers $A,m\ge1$ and let $S=\{0\}\cup[A]$. Let $h:S^m\to[0,1]$ be invariant under permutations of its coordinates and put $q_w(s)=h(w,s)$ for $w\in S^{m-1}$. Let $(\pi_u)_{0\le u\le1}$ be a continuous, piecewise $C^1$ path of probability distributions on $S$ whose moments through order $r-1$ are constant in $u$, for an integer $r\ge1$, and let $F(u)=\mathbb E_{\pi_u^{\otimes m}}[h]$. For each $w\in S^{m-1}$ let $P_w$ be a real polynomial of degree below $r$. Then for every $G\subseteq S^{m-1}$,
--   $$|F(1)-F(0)|\le m\int_0^1\mathbb E_{w\sim\pi_u^{\otimes(m-1)}}\Big[\mathbf 1_G\Big|\sum_{s\in S}\dot\pi_u(s)\big(q_w(s)-P_w(s)\big)\Big|\Big]du+m\int_0^1\|\dot\pi_u\|_1\Pr_{w\sim\pi_u^{\otimes(m-1)}}[w\notin G]\,du,\tag{15}$$
--   where $\dot\pi_u(s)=\frac{d}{du}\pi_u(s)$ and $\|\dot\pi_u\|_1=\sum_{s\in S}|\dot\pi_u(s)|$.
--
--   Moment matching lets one subtract any low-degree polynomial from $q_w$ in the hybrid bound; the complement of $G$ contains the choices of $w$ where the approximation is not controlled.
--
--   **Formalization Note** "Moments constant in $u$" is $\sum_s\pi_u(s)s^k=\sum_s\pi_v(s)s^k$ for all $u,v\in[0,1]$ and $1\le k\le r-1$. $\dot\pi_u$ is Lean's `deriv`, which can differ from the one-sided derivatives only at the finitely many breakpoints.
--
--   Differences from the source:
--   - encoding: $S^{m-1}$ and $(w,s)$ → `Fin (m - 1) → S` and `appendLast w s`; reason: the source moves the chosen coordinate to the last position (p. 18).
--   - encoding: "continuous, piecewise $C^1$" → coordinates continuous on $[0,1]$ and $C^1$ on each closed piece of a finite partition; reason: the standard meaning, made explicit; it makes the integrands integrable.
--   - encoding: $\dot\pi_u$ → `deriv`; reason: it agrees with the derivative off the finitely many breakpoints, which do not change the integrals.
--   - encoding: $G\subseteq S^{m-1}$ → a `Finset` of `Fin (m - 1) → S`; reason: every subset of a finite set is a finite set.
--   - encoding: distributions on S = {0} ∪ [A] → real probability vectors on Fin (A + 1); reason: finite laws and expectations are represented by the same masses and finite sums.
-- source:
--   Chandrima Kayal, Frédéric Magniez, Sayantan Sen, Dániel Szabó, STOC 2027 submission #564 (October 2026), §3.2 standing setting p. 18, Lemma 3.8, p. 20

import Mathlib
import Definitions.Def_QMomentMatch_FirstBound_Basic

namespace QMomentMatch.FirstBound

/-- Lemma 3.8, p. 20, in the standing setting of §3.2 (integers `A, m ≥ 1`, `S = {0} ∪ [A]`),
with `π̇_u(s) = d/du π_u(s)` and `‖π̇_u‖₁ = ∑_s |π̇_u(s)|`. -/
theorem lemma_3_8 (A m r : ℕ) (hA : 1 ≤ A) (hm : 1 ≤ m) (hr : 1 ≤ r)
    (h : (Fin m → Fin (A + 1)) → ℝ) (h01 : ∀ z, h z ∈ Set.Icc (0 : ℝ) 1)
    (hsymm : ∀ (σ : Equiv.Perm (Fin m)) (z : Fin m → Fin (A + 1)), h (z ∘ σ) = h z)
    (π : ℝ → Fin (A + 1) → ℝ) (hπ : IsPiecewiseC1ProbPath π)
    (hmom : ∀ k : ℕ, 1 ≤ k → k ≤ r - 1 →
      ∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ v ∈ Set.Icc (0 : ℝ) 1, moment (π u) k = moment (π v) k)
    (P : (Fin (m - 1) → Fin (A + 1)) → Polynomial ℝ) (hP : ∀ w, (P w).degree < r)
    (G : Finset (Fin (m - 1) → Fin (A + 1))) :
    |prodExp (π 1) h - prodExp (π 0) h| ≤
      (m : ℝ) * (∫ u in (0 : ℝ)..1, prodExp (π u) fun w : Fin (m - 1) → Fin (A + 1) =>
        if w ∈ G then
          |∑ s, deriv (fun v => π v s) u * (h (appendLast w s) - (P w).eval ((s : ℕ) : ℝ))|
        else 0) +
      (m : ℝ) * ∫ u in (0 : ℝ)..1, (∑ s, |deriv (fun v => π v s) u|) *
        prodExp (π u) fun w : Fin (m - 1) → Fin (A + 1) => if w ∈ G then 0 else 1 := by sorry

end QMomentMatch.FirstBound
