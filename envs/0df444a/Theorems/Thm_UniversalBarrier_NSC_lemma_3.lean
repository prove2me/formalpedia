-- Prove2me | Theorems.Thm_UniversalBarrier_NSC_lemma_3
-- name    : UniversalBarrier.NSC.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:36:39.872425+00:00
-- url     : https://prove2.me/theorems/5cbd9780-15c2-4143-a479-131938bedbf6
-- title:
--   Lemma 3, p. 16 — Q and Ξ are invariant under affine reparametrization
-- statement:
--   Let $k\ge2$ be an integer and let $p$ be a $\tfrac1{k-1}$-affine density, $p\in\mathcal Q$, i.e. $p(t)=(\alpha t+\beta)^{k-1}\mathbb 1_{[a,b]}(t)/\int_a^b(\alpha u+\beta)^{k-1}du$ with $a<b$ and $\alpha t+\beta\ge0$ on $[a,b]$. Let $\tilde\alpha,\tilde\beta\in\mathbb R$ with $\tilde\alpha\neq0$ and $\tilde p(t)=|\tilde\alpha|\,p(\tilde\alpha t+\tilde\beta)$. Then
--   $$\tilde p\in\mathcal Q\qquad\text{and}\qquad \Xi(p)=\Xi(\tilde p),$$
--   where $\Xi(p)=\bigl|\mu_3^3(p)/\mu_2^3(p)\bigr|$.
--
--   The lemma lets the proof of inequality (4) reduce to the normalized densities $k t^{k-1}\mathbb 1_{[0,1]}$ and $t^{k-1}\mathbb 1_{[1,\gamma]}$ (up to normalization).
--
--   **Formalization Note.** $\mathcal Q$ is taken with $a<b$ (the paper sets the degenerate case $a=b$ aside as trivial on the same page). $\mu_2^3(p)=(\mu_2^2(p))^{3/2}$.
-- source:
--   Lee & Yue, Universal Barrier is n-Self-Concordant, arXiv:1809.03011v4, p. 16, Lemma 3; (10), p. 7; definition of Ξ, p. 13

import Mathlib
import Definitions.Def_UniversalBarrier_NSC_Model

namespace UniversalBarrier.NSC

theorem lemma_3 (k : ℕ) (hk : 2 ≤ k) (p : ℝ → ℝ) (hp : IsKAffine k p) (α' β' : ℝ) (hα' : α' ≠ 0) :
    IsKAffine k (fun t => |α'| * p (α' * t + β')) ∧
      Xi p = Xi (fun t => |α'| * p (α' * t + β')) := by sorry

end UniversalBarrier.NSC
