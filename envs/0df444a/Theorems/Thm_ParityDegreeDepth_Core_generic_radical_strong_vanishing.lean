-- Prove2me | Theorems.Thm_ParityDegreeDepth_Core_generic_radical_strong_vanishing
-- name    : ParityDegreeDepth.Core.generic_radical_strong_vanishing
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T03:58:36.006094+00:00
-- url     : https://prove2.me/theorems/2ca30fbf-67ca-5a11-9067-1d6e0c924e5e
-- title:
--   Theorem 3.5 (polynomial form): the generic radical satisfies $T(K^n,U,\dots,U)=0$
-- statement:
--   Let $T$ be a symmetric $d$-linear form on $\mathbb F_2^n$ with $d=m+3\ge 3$, given by a symmetric coefficient tensor $c:[n]^d\to\mathbb F_2$ (that is, $c(a\circ\sigma)=c(a)$ for every permutation $\sigma$ of the $d$ slots). Introduce $m+1=d-2$ blocks of independent indeterminates $t_\ell=(t_{\ell,1},\dots,t_{\ell,n})$ and let $P=\mathbb F_2[t_{\ell,v}]$ with fraction field $K$. Consider the generic contraction matrix
--
--   $$
--   A_{ij}\;=\;T\big(t_1,\dots,t_{d-2},e_i,e_j\big)\in P,\qquad R=\operatorname{rank}_K A .
--   $$
--
--   Then there are $r$ with $r+R=n$ and an $n\times r$ matrix $\Lambda$ with entries in $P$ having a nonzero $r\times r$ minor, such that
--
--   $$
--   T(v,\lambda_1,\dots,\lambda_{d-1})=0\qquad\text{for every } v\in P^n \text{ and all columns } \lambda_1,\dots,\lambda_{d-1} \text{ of } \Lambda .
--   $$
--
--   Since the columns of $\Lambda$ are $K$-linearly independent and lie in the radical $U=\ker_K A$, which has dimension $n-R=r$, they form a basis of $U$; by multilinearity this is exactly the strong vanishing identity $T(K^n,U,\dots,U)=0$ of Theorem 3.5, with $\dim_K U=n-R$. The conclusion is stronger than $T(U,\dots,U)=0$ because one argument ranges over the whole space.
--
--   **Formalization Note** The form is evaluated via `ParityDegreeDepth.Core.tensorEval`; the first $d-2$ slots carry the anchors $t_\ell$ (variable `X (l, v)`), the last two slots carry $e_i,e_j$. The basis is given by polynomial vectors, which is how it is consumed by the descent Lemma 3.7.
-- source:
--   Zhang, Parity Decision Trees of Depth O(4^d log ||f^||_1) for Boolean Functions f of F2-Degree d, STOC 2027 submission #798, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/798.pdf, §3.4, Theorem 3.5, pp. 6-9 (proof: perturbation, Schur complement eq. (11), simultaneous induction (1)/(2))

import Mathlib
import Definitions.Def_ParityDegreeDepth_Core_tensorEval

open ParityDegreeDepth.Core

theorem ParityDegreeDepth.Core.generic_radical_strong_vanishing {n m : ℕ}
    (c : (Fin (m + 1 + 2) → Fin n) → ZMod 2)
    (hc : ∀ (σ : Equiv.Perm (Fin (m + 1 + 2))) (a : Fin (m + 1 + 2) → Fin n), c (a ∘ σ) = c a) :
    ∃ (r : ℕ) (Λ : Matrix (Fin n) (Fin r) (MvPolynomial (Fin (m + 1) × Fin n) (ZMod 2))),
      r + ((Matrix.of fun i j : Fin n => tensorEval c
          (Fin.append (fun l v => (MvPolynomial.X (l, v) : MvPolynomial (Fin (m + 1) × Fin n) (ZMod 2)))
            ![Pi.single i 1, Pi.single j 1])).map
          (algebraMap (MvPolynomial (Fin (m + 1) × Fin n) (ZMod 2))
            (FractionRing (MvPolynomial (Fin (m + 1) × Fin n) (ZMod 2))))).rank = n ∧
      (∃ ρ : Fin r → Fin n, (Λ.submatrix ρ id).det ≠ 0) ∧
      ∀ x : Fin (m + 1 + 2) → Fin n → MvPolynomial (Fin (m + 1) × Fin n) (ZMod 2),
        (∀ j, j ≠ 0 → ∃ l, x j = fun i => Λ i l) → tensorEval c x = 0 := by sorry
