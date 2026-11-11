-- Prove2me | Theorems.Thm_UPPIntersection_Halfspaces_theorem_4_3
-- name    : UPPIntersection.Halfspaces.theorem_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T16:27:38.255862+00:00
-- url     : https://prove2.me/theorems/34979874-b729-4373-b4b4-62d46cc84727
-- title:
--   Theorem 4.3 — Sherstov: rational approximations from a sign representation of a conjunction
-- statement:
--   Let $f_1,\dots,f_k$ be Boolean functions ($\pm1$-valued) on nonempty compact sets $X_1,\dots,X_k\subseteq\mathbb R$, none identically $+1$ (each takes the value $-1$ somewhere on its domain). Let $D=\deg_\pm\bigl(\bigwedge_i f_i\bigr)$ be the least total degree of a real polynomial $P$ in $k$ variables with $P(x)\cdot\bigwedge_i f_i(x_i)>0$ for all $x\in X_1\times\dots\times X_k$. Then there are univariate polynomials $p_1,\dots,p_k,q_1,\dots,q_k$ of degree at most $12D\ln(2k)$ such that $q_i(x)>0$ for all $i$ and $x\in X_i$, and
--   $$\sum_{i=1}^k\ \sup_{x\in X_i}\Bigl|f_i(x)-\frac{p_i(x)}{q_i(x)}\Bigr|<1 .$$
--
--   The domains may be infinite (the source's footnote extends Sherstov's finite-domain theorem to compact sets). In Lemma 4.4 this converts a sign representation of $Q_k$ into a rational approximation of $\operatorname{sgn}$ on $I_\eta$.
--
--   Differences from the source:
--   - encoding: D = deg±(⋀ f_i) → any natural D for which some polynomial of total degree ≤ D sign-represents ⋀ f_i on X_1 × … × X_k; reason: the conclusion only weakens as D grows, so the source's case D = deg± (attained by a representation) gives every such D, and the case of the minimal D is the source's statement; if no sign representation exists the hypothesis is never met, as the source's D would be infinite
--   - encoding: sum over i of sup over X_i of |f_i − p_i/q_i| is < 1 → there are reals ε_i with |f_i(x) − p_i(x)/q_i(x)| ≤ ε_i on X_i and ∑ ε_i < 1; reason: each supremum is finite (f_i is ±1-valued and p_i/q_i is continuous on the compact X_i where q_i > 0), so choosing ε_i the supremum shows the two are equivalent
--   - encoding: f_i : X_i → {−1, 1} → f_i : ℝ → ℝ with f_i(x) ∈ {1, −1} for x ∈ X_i; values off X_i are never used; reason: same functions on the domains
-- source:
--   Mark Bun, Mandar Juvekar, STOC 2027 submission #478 (October 2026), p. 21, Theorem 4.3 and footnote 3 ([She13a, Theorem 3.17]); PDF page = printed page; source.pdf SHA-256 1d258c38a48636b0aa03fa9dfce0ba5e367df8b9c55ee6e67f9f3b6f76e0d388

import Mathlib
import Definitions.Def_UPPIntersection_Halfspaces_Polynomials

namespace UPPIntersection.Halfspaces

theorem theorem_4_3 (k : ℕ) (X : Fin k → Set ℝ)
    (hXne : ∀ i, (X i).Nonempty) (hXc : ∀ i, IsCompact (X i))
    (f : Fin k → ℝ → ℝ) (hfb : ∀ i, ∀ x ∈ X i, f i x = 1 ∨ f i x = -1)
    (hf1 : ∀ i, ∃ x ∈ X i, f i x = -1)
    (D : ℕ) (P : MvPolynomial (Fin k) ℝ) (hPdeg : P.totalDegree ≤ D)
    (hP : ∀ x : Fin k → ℝ, (∀ i, x i ∈ X i) →
      0 < MvPolynomial.eval x P * signedAnd (fun i => f i (x i))) :
    ∃ p q : Fin k → Polynomial ℝ,
      (∀ i, ((p i).natDegree : ℝ) ≤ 12 * D * Real.log (2 * k)) ∧
      (∀ i, ((q i).natDegree : ℝ) ≤ 12 * D * Real.log (2 * k)) ∧
      (∀ i, ∀ x ∈ X i, 0 < (q i).eval x) ∧
      ∃ ε : Fin k → ℝ, (∀ i, ∀ x ∈ X i, |f i x - (p i).eval x / (q i).eval x| ≤ ε i) ∧
        ∑ i, ε i < 1 := by sorry

end UPPIntersection.Halfspaces
