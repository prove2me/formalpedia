-- Prove2me | Theorems.Thm_TemperleyLieb_Gram_corollary_3_7
-- name    : TemperleyLieb.Gram.corollary_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:45:39.504792+00:00
-- url     : https://prove2.me/theorems/2ef1769e-c557-40ee-9ece-54ac39d908e0
-- title:
--   Corollary 3.7, p. 16 — z_t(k) = p_i p_{k−i+1} and the triangular action of z_k
-- statement:
--   Let $\lambda=(f,n-2f)$ be a partition of $n$ and $\mathfrak t\in\mathfrak T_n(\lambda)$, and let $0\le k\le n$. Let $r_{\mathfrak t}(k)$ be the contents of p. 15 and $z_{\mathfrak t}(k)=\sum_{i=0}^k x^ir_{\mathfrak t}(k-i)$. If $\operatorname{Shape}(\mathfrak t|_k)=(i,k-2i)$, then
--
--   $$z_{\mathfrak t}(k)=p_ip_{k-i+1},$$
--
--   and there are $a_{\mathfrak s}\in R$ such that, in the cell module $C^\lambda$,
--
--   $$m_{\mathfrak t}z_k=z_{\mathfrak t}(k)\,m_{\mathfrak t}+\sum_{\mathfrak s\triangleright\mathfrak t}a_{\mathfrak s}m_{\mathfrak s},$$
--
--   where $m_{\mathfrak t}=m_\lambda v_{\mathfrak t}+\check A^\lambda_n$. The central elements thus act triangularly on the Murphy basis of the cell module with diagonal entries depending only on the shape at stage $k$.
--
--   **Formalization Note** The congruence is stated in $A_n(x)$, modulo the span of the Murphy elements of shapes with more cups, with $m_{\mathfrak t}$ represented by $m_\lambda v_{\mathfrak t}$. The dominance $\mathfrak s\triangleright\mathfrak t$ is the pointwise order on cup-count paths (`t < s`). The number of cups at stage $k$ is `cups t k`.
-- source:
--   Enyang, Representations of Temperley–Lieb Algebras, arXiv:0710.3218v1, p. 16, Corollary 3.7 and definition of z_t(k); p. 15, definition of r_t(k)

import Mathlib
import Definitions.Def_TemperleyLieb_Gram_Models

namespace TemperleyLieb.Gram
open QAlgorithms.Papers.Independent.Support21.P08
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Enyang, Corollary 3.7, p. 16: the cumulative content `z_t(k)` equals
`p_i p_{k-i+1}` where `i` is the number of cups of `t` at stage `k`, and `z_k`
acts on `m_t = m_λ v_t + Ǎ^λ_n` triangularly with that diagonal entry. -/
theorem corollary_3_7 (n : ℕ) (f : Fin (n / 2 + 1)) (t : Tab n f) (k : ℕ) (hk : k ≤ n) :
    zt t k = p (cups t k) * p (k - cups t k + 1) ∧
    ∃ a : Tab n f → R,
      mLam R Polynomial.X n f * vElt R Polynomial.X t * zJM R Polynomial.X n k -
          zt t k • (mLam R Polynomial.X n f * vElt R Polynomial.X t) -
          ∑ s ∈ Finset.univ.filter (fun s : Tab n f => t < s),
            a s • (mLam R Polynomial.X n f * vElt R Polynomial.X s) ∈
        higherSpan (R := R) (murphy R Polynomial.X n) f := by sorry

end TemperleyLieb.Gram
