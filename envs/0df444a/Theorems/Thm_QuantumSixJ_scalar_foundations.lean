-- Prove2me | Theorems.Thm_QuantumSixJ_scalar_foundations
-- name    : QuantumSixJ.scalar_foundations
-- status  : Proved
-- author  : @igor.kh
-- created : 2026-11-13T00:44:02.876206+00:00
-- url     : https://prove2.me/theorems/846e4eb0-6e53-42fe-892f-73c9dd87c00e
-- title:
--   Appendix — scalar foundations and support identities
-- statement:
--   Over $\mathbb Q(q)$, with $q$ an indeterminate, establish the scalar foundations for the Appendix formulas. The nonzero quantities are $q$, $q-q^{-1}$, $[n]$ for every nonzero integer $n$, $[n]!$ for every nonnegative integer $n$, $\Delta_j$ for $j\ge0$, $\theta(a,b,c)$ on admissible triples, and the norms $h_j,x_l$ on their respective admissible channels.
--
--   Under both horizontal and vertical admissibility, let $A_i,B_k$ be the Appendix half-sums, $m=\max_i A_i$, and $M=\min_k B_k$. For every integer summation index $S$, the raw factorial summand is nonzero exactly when $m\le S\le M$, and
--   $$0\le m\le M\le a+b+c+d+j+l.$$
--   Thus its effective Appendix support lies inside the coarse defining finite interval.
--
--   In addition, the explicitly defined two-index matrix satisfies $L_{jk}=L_{kj}$, is zero unless $k\in\{j-2,j,j+2\}$, and has $L_{00}=0$, for all integer labels, including zero-extended cases. No recurrence or categorical assumptions occur in this statement.
--
--   ### Independent mathematical read-back
--
--   # Scalar foundations
--
--   All labels below are integers. Scalars belong to the rational-function field \(\mathbb Q(q)\), with \(q\) an indeterminate. Write
--   \[
--   [n]=\frac{q^n-q^{-n}}{q-q^{-1}},\qquad
--   [n]!=\begin{cases}\prod_{t=1}^n[t],&n\ge0,\\0,&n<0.\end{cases}
--   \]
--   In particular, \([0]!=1\). Integer powers, including negative powers, are interpreted in this field. Division is total: division by zero is zero. These conventions concern rational functions and integer labels, not specialization of \(q\) at numerical poles.
--
--   A triple \((a,b,c)\) is **admissible** precisely when all three entries are nonnegative, each is at most the sum of the other two, and \(a+b+c\) is even. Put
--   \[
--   H(a,b,c,d;j)\iff(a,d,j),(b,c,j)\text{ are admissible},
--   \]
--   \[
--   V(a,b,c,d;l)\iff(a,b,l),(c,d,l)\text{ are admissible}.
--   \]
--   Define \(\Delta_j=(-1)^j[j+1]\) for \(j\ge0\), and zero otherwise. For an admissible triple, with \(s=(a+b+c)/2\), define
--   \[
--   \theta(a,b,c)=(-1)^s\frac{[s+1]![s-a]![s-b]![s-c]!}{[a]![b]![c]!};
--   \]
--   set \(\theta=0\) for an inadmissible triple. The norms are
--   \[
--   h(a,b,c,d;j)=\frac{\theta(a,d,j)\theta(b,c,j)}{\Delta_j}
--   \quad\text{when }H(a,b,c,d;j),
--   \]
--   \[
--   x(a,b,c,d;l)=\frac{\theta(a,b,l)\theta(c,d,l)}{\Delta_l}
--   \quad\text{when }V(a,b,c,d;l),
--   \]
--   and zero outside their respective admissible domains.
--
--   For six labels define the four entries of \(A\) and the three entries of \(B\), in order, by
--   \[
--   A=\left(\frac{a+d+j}{2},\frac{b+c+j}{2},\frac{a+b+l}{2},\frac{c+d+l}{2}\right),\qquad
--   B=\left(\frac{b+d+j+l}{2},\frac{a+c+j+l}{2},\frac{a+b+c+d}{2}\right).
--   \]
--   All divisions producing integer labels mean integer division; on the admissible domain the displayed half-sums are integral. The raw summand is
--   \[
--   F_{abcdjl}(S)=\frac{(-1)^S[S+1]!}{\prod_{i=0}^3[S-A_i]!\prod_{t=0}^2[B_t-S]!}.
--   \]
--   There is no separate support guard in this expression: a negative denominator-factorial argument makes the denominator zero and hence the quotient zero.
--
--   The scalar-foundations assertion is the conjunction of the following thirteen clauses:
--
--   1. \(q\ne0\).
--   2. \(q-q^{-1}\ne0\).
--   3. For every integer \(n\ne0\), \([n]\ne0\).
--   4. For every integer \(n\ge0\), \([n]!\ne0\).
--   5. For every integer \(j\ge0\), \(\Delta_j\ne0\).
--   6. For every admissible integer triple \((a,b,c)\), \(\theta(a,b,c)\ne0\).
--   7. For every five integers \(a,b,c,d,j\) satisfying \(H(a,b,c,d;j)\), \(h(a,b,c,d;j)\ne0\).
--   8. For every five integers \(a,b,c,d,l\) satisfying \(V(a,b,c,d;l)\), \(x(a,b,c,d;l)\ne0\).
--   9. For every seven integers \(a,b,c,d,j,l,S\), assuming both \(H(a,b,c,d;j)\) and \(V(a,b,c,d;l)\), set
--      \[
--      m=\max(A_0,A_1,A_2,A_3),\qquad M=\min(B_0,B_1,B_2).
--      \]
--      Then \(F_{abcdjl}(S)\ne0\) if and only if \(m\le S\le M\). This quantifies over every integer \(S\), not merely over a defining finite summation range.
--   10. For every six integers \(a,b,c,d,j,l\) satisfying the same two admissibility hypotheses,
--       \[
--       0\le m\le M\le a+b+c+d+j+l.
--       \]
--   11. For every six integers \(a,b,c,d,j,k\), without admissibility hypotheses,
--       \(L(a,b,c,d;j,k)=L(a,b,c,d;k,j)\).
--   12. For every six integers \(a,b,c,d,j,k\), if \(k\ne j\), \(k\ne j-2\), and \(k\ne j+2\), then \(L(a,b,c,d;j,k)=0\).
--   13. For every four integers \(a,b,c,d\), \(L(a,b,c,d;0,0)=0\).
--
--   The matrix used here is specified independently as follows. Set
--   \[
--   \Lambda(a,b,l)=\frac{[(a-b+l)/2][(-a+b+l)/2]-[(a+b-l)/2][(a+b+l)/2+2]}{[2]}
--   \]
--   on admissible triples, and zero otherwise. On the diagonal,
--   \[
--   L(a,b,c,d;j,j)=-\frac{h(a,b,c,d;j)[2]\Lambda(a,j,d)\Lambda(b,j,c)}{[j][j+2]}
--   \]
--   if \(H(a,b,c,d;j)\) and \(j\ne0\), and zero otherwise. If \(|j-k|=2\), let \(p=\min(j,k)\), \(r=\max(j,k)\). When both horizontal channels \(p,r\) are admissible,
--   \[
--   L(a,b,c,d;j,k)=h(a,b,c,d;r)[(a+d-p)/2][(b+c-p)/2];
--   \]
--   otherwise it is zero. All remaining entries are zero. In particular, the \((0,0)\) value is an explicit zero branch, not a cancellation across a vanishing denominator.
-- source:
--   I. Khavkine, Recurrence relation for the 6j-symbol of su_q(2) as a symmetric eigenvalue problem, International Journal of Geometric Methods in Modern Physics (2015), https://doi.org/10.1142/S0219887815501170; https://arxiv.org/abs/1009.2261. Appendix quantum integers, factorials, admissibility, loop/theta/norm formulas and finite Tet formula; Eqs. (19), (20), symmetric matrix coefficients.

import Definitions.Def_QuantumSixJScalar

open scoped BigOperators QuantumSixJ

namespace QuantumSixJ

theorem scalar_foundations :
    (q ≠ 0) ∧
    (q - q⁻¹ ≠ 0) ∧
    (∀ n : ℤ, n ≠ 0 → ⟬n⟭ ≠ 0) ∧
    (∀ n : ℤ, 0 ≤ n → ⟬n⟭! ≠ 0) ∧
    (∀ j : ℤ, 0 ≤ j → Δ j ≠ 0) ∧
    (∀ a b c : ℤ, Admissible a b c → θ a b c ≠ 0) ∧
    (∀ a b c d j : ℤ, hAdmissible a b c d j → h a b c d j ≠ 0) ∧
    (∀ a b c d l : ℤ, vAdmissible a b c d l → x a b c d l ≠ 0) ∧
    (∀ a b c d j l S : ℤ, hAdmissible a b c d j → vAdmissible a b c d l →
      let A := tetA a b c d j l
      let B := tetB a b c d j l
      let m := max (max (A 0) (A 1)) (max (A 2) (A 3))
      let M := min (B 0) (min (B 1) (B 2))
      tetSummand a b c d j l S ≠ 0 ↔ m ≤ S ∧ S ≤ M) ∧
    (∀ a b c d j l : ℤ, hAdmissible a b c d j → vAdmissible a b c d l →
      let A := tetA a b c d j l
      let B := tetB a b c d j l
      let m := max (max (A 0) (A 1)) (max (A 2) (A 3))
      let M := min (B 0) (min (B 1) (B 2))
      0 ≤ m ∧ m ≤ M ∧ M ≤ a + b + c + d + j + l) ∧
    (∀ a b c d j k : ℤ, L a b c d j k = L a b c d k j) ∧
    (∀ a b c d j k : ℤ, k ≠ j → k ≠ j - 2 → k ≠ j + 2 → L a b c d j k = 0) ∧
    (∀ a b c d : ℤ, L a b c d 0 0 = 0) := by sorry

end QuantumSixJ
