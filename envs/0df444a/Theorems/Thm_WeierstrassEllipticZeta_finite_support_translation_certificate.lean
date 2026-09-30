-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_finite_support_translation_certificate
-- name    : WeierstrassEllipticZeta.finite_support_translation_certificate
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-13T03:58:21.346014+00:00
-- url     : https://prove2.me/theorems/9d4258e5-6af1-4dfd-afba-48c5e96422a9
-- title:
--   Finite admissible translations characterize supported monomial multiples
-- statement:
--   Let $K$ be a field, $p\in K[\sigma]$ a nonzero polynomial, and $S\subseteq\mathbb N^{(\sigma)}$ a finite exponent set. Define the set of admissible translations
--   $$E(p,S)=\{d\in\mathbb N^{(\sigma)}:\ e+d\in S\text{ for every }e\in\operatorname{supp}(p)\}.$$
--   Then $E(p,S)$ is finite, $|E(p,S)|\le |S|$, and for every exponent $d$,
--   $$\operatorname{supp}(pX^d)\subseteq S\quad\Longleftrightarrow\quad d\in E(p,S).$$
--   The variable set may be infinite, and $S$ may be empty. The statement does not assume that admissible translations themselves belong to $S$.
-- source:
--   Derived support-translation certificate for the frontier https://prove2.me/theorems/a0d7189b-1242-47eb-bf90-6587bb9a2e25. The mission setting is Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2 and Theorem A.2, https://doi.org/10.1017/S001309152610145X. The supporting result uses the exact coefficient formula for multiplication by a monomial and injectivity of translation on exponent vectors in Mathlib commit 0df444a360eaa60ab8c11dca51a86af692955474. The uniform geometric counting bound remains open.

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Set.Card

open scoped Pointwise

noncomputable section

theorem WeierstrassEllipticZeta.finite_support_translation_certificate
    (K σ : Type*) [Field K] (p : MvPolynomial σ K) (hp : p ≠ 0)
    (S : Finset (σ →₀ ℕ)) :
    let E : Set (σ →₀ ℕ) := {d | ∀ e ∈ p.support, e + d ∈ S}
    E.Finite ∧ E.ncard ≤ S.card ∧
      ∀ d : σ →₀ ℕ, (p * MvPolynomial.monomial d 1).support ⊆ S ↔ d ∈ E := by sorry
