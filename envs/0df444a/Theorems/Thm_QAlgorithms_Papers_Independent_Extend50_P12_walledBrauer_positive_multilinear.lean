-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P12_walledBrauer_positive_multilinear
-- name    : QAlgorithms.Papers.Independent.Extend50.P12.walledBrauer_positive_multilinear
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:48:34.309148+00:00
-- url     : https://prove2.me/theorems/37862cb2-a9c7-47ef-b031-f58ab2409328
-- title:
--   Main construction: positive multilinear maps from the displayed walled-Brauer projectors, Eq.(53)
-- statement:
--   Let $d\ge1$, $a\ge0$, and $k\ge1$ be integers, and put $N=a+2k$. Let $\alpha\vdash a$ and $\mu\vdash a+k$ be Young diagrams of height at most $d$, with $\alpha\subseteq\mu$. Thus $\mu$ has exactly $k$ additional boxes. Let $P_\lambda$ denote the full physical Schur–Weyl isotypic projector, $d_\lambda$ the Specht dimension, and $m_\lambda$ its multiplicity on tensor space. These objects are constructed from the Young modules and character formula (A6).
--
--   In the fixed product basis define
--   $$
--   \sigma^{(k)}=\prod_{j=1}^{k}V(a+j,N+1-j)^{T_{N+1-j}},\qquad
--   \gamma_\mu(\alpha)=k!\binom{a+k}{k}\frac{m_\mu d_\alpha}{m_\alpha d_\mu},
--   $$
--   and construct the physical operator
--   $$
--   F_\mu(\alpha)=\frac{1}{\gamma_\mu(\alpha)}P_\mu
--   \sum_{\eta\in S_{a+k}/S_a}\eta^{-1}(P_\alpha\otimes\sigma^{(k)})\eta.
--   $$
--   The projectors and permutations are extended by identity on their remaining sites. The permutation action is $V(\eta)|v_1\cdots v_N\rangle=|v_{\eta^{-1}(1)}\cdots v_{\eta^{-1}(N)}\rangle$; $T_j$ means ordinary partial transpose. For any integers $r,m\ge1$ with $r+m=N$, the map
--   $$
--   \Lambda_{\alpha,\mu}(X_1,\ldots,X_r)
--   =\operatorname{tr}_{1\cdots r}\!\left[F_\mu(\alpha)(X_1\otimes\cdots\otimes X_r\otimes I^{\otimes m})\right]
--   $$
--   is complex linear in each input separately and is positive: its output is PSD whenever all $X_i\in M_d(\mathbb C)$ are PSD. Input traces are unrestricted and the partial trace is unnormalized.
--
--   This constructs positive maps from the maximal-contraction sector; it does not classify every mixed irreducible module.
--
--   **Formalization Note** The coset sum is represented by the full $S_{a+k}$ conjugation sum divided by $a!$. The core is invariant under conjugation by $S_a$, so this removes exactly the repetition of each coset. The total system count and input count are distinct variables.
-- source:
--   Positive maps from the walled Brauer algebra, arXiv:2112.12738v3, PDF p. 9, Eqs.(51)-(53), (A6), (A11)-(A12)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P12

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P12

attribute [local instance] Classical.propDecidable

/-- Main construction, PDF pp.8-9, Eqs.(51)-(53), and pp.11-12, Eqs.(A6),(A11),
(A12). N=a+2k, with a possibly zero, k>=1, d>=1; alpha is contained in mu
with k added boxes, and both heights are bounded by d. For ANY nonempty input
and output groups, the explicitly constructed kernel gives a complex multilinear
positive map. This asserts product-input positivity, not Section V's undefined
complete-positivity amplification. Only the maximal-productInputContraction sector is used. -/
theorem walledBrauer_positive_multilinear
    (d a k r m : ℕ) (hd : 0 < d) (hk : 0 < k) (hr : 0 < r) (hm : 0 < m)
    (htotal : r + m = a + 2 * k)
    (alpha : QAlgorithms.Schur.Partition d a)
    (mu : QAlgorithms.Schur.Partition d (a + k))
    (hcontains : alpha.val.cells ⊆ mu.val.cells) :
    ComplexMultilinear (walledMap htotal alpha mu) ∧
      PositiveMap (walledMap htotal alpha mu) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P12

end
