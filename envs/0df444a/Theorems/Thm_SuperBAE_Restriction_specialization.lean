-- Prove2me | Theorems.Thm_SuperBAE_Restriction_specialization
-- name    : SuperBAE.Restriction.specialization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:25:23.636217+00:00
-- url     : https://prove2.me/theorems/34a33189-ec91-41ce-ba38-b0080ba6914a
-- title:
--   §4.1, p. 17 (PDF 18) — under A1–A2 the BAE for α_{k−1}, α_k, α_{k+1} take the forms (4.2), (4.3), (4.4)
-- statement:
--   Consider the Bethe ansatz equations (2.9) of the homogeneous $\mathfrak{gl}(M|N)$ chain of length $L$ in a grading $\sigma_1,\dots,\sigma_d$ ($d=M+N$, rank $r=d-1$), with loop weight $n=M-N>0$. Fix a simple root $\alpha_k$ such that
--
--   1. **A1** $\alpha_k$ is odd: $\sigma_k\sigma_{k+1}=-1$;
--   2. **A2** $\alpha_k$ has no source terms: $k\neq 1, r$, i.e. $2\le k\le d-2$.
--
--   Suppose the root family is regular. Then $\Lambda_k=\Lambda_{k+1}$, $\sigma_{k+1}=-\sigma_k$, and
--
--   $$\begin{aligned}
--   &\text{for every root } u \text{ of type } k-1: && (2.9)_{k-1}\text{ at } u \iff (4.2)\text{ at } u,\\
--   &\text{for every root } u \text{ of type } k: && (2.9)_{k}\text{ at } u \iff (4.3)\text{ at } u,\\
--   &\text{for every root } u \text{ of type } k+1: && (2.9)_{k+1}\text{ at } u \iff (4.4)\text{ at } u,
--   \end{aligned}$$
--
--   where (4.2)–(4.4) are the equations printed on p. 17 (see the definitions file).
--
--   This is the specialization of the nested system to the three simple roots around an odd, sourceless $\alpha_k$; it is the starting point of the restriction procedure R1–R2.
--
--   **Formalization Note.** Regularity (nonzero source terms and nonzero denominators of (2.9) at every root) is added: it is the non-degeneracy that the division form of (2.9) presupposes, and it is needed to clear $\Lambda_k(u)/\Lambda_{k+1}(u)=1$ and the common factor $Q_k(u-\sigma_k)$ in the type-$k$ equation. The standing assumption $n=M-N>0$ of p. 7 is stated as $N<M$; the algebra of §4 does not use it. The page says "$\nu^{(k)}$ BAE for $\alpha_{k-1}$", a slip for $\nu^{(k-1)}$; the statement quantifies over the roots of type $k-1$.
-- source:
--   Candu, Continuum Limit of gl(M|N) Spin Chains, arXiv:1012.0050v1, p. 17 (PDF 18), §4.1, A1, A2, eqs. (4.2)–(4.4); standing assumption n = M − N > 0, p. 7 (PDF 8)

import Mathlib
import Definitions.Def_SuperBAE_Restriction_Model

namespace SuperBAE.Restriction

theorem specialization (L : ℕ) (odd : ℕ → Bool) (d : ℕ) (roots : ℕ → Finset ℂ) (k : ℕ)
    (hA1 : odd k ≠ odd (k + 1)) (hA2k : 2 ≤ k) (hA2d : k + 2 ≤ d)
    (hn : numOdd odd d < numEven odd d)
    (hreg : Regular L odd d roots) :
    lam L odd d k = lam L odd d (k + 1) ∧ sgn odd (k + 1) = -sgn odd k ∧
      (∀ u ∈ roots (k - 1), bae L odd d roots (k - 1) u ↔ eq4_2 L odd d roots k u) ∧
      (∀ u ∈ roots k, bae L odd d roots k u ↔ eq4_3 d odd roots k u) ∧
      (∀ u ∈ roots (k + 1), bae L odd d roots (k + 1) u ↔ eq4_4 L odd d roots k u) := by sorry

end SuperBAE.Restriction
