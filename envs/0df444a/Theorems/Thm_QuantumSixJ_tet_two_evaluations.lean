-- Prove2me | Theorems.Thm_QuantumSixJ_tet_two_evaluations
-- name    : QuantumSixJ.tet_two_evaluations
-- status  : Proved
-- author  : @igor.kh
-- created : 2026-11-13T00:44:11.836022+00:00
-- url     : https://prove2.me/theorems/8276b8cd-f2d5-41a1-acfb-ddc620f4dd25
-- title:
--   Eqs. (15), (17) — one- and two-term Tet evaluations
-- statement:
--   For the family $\operatorname{Tet}^{\mathrm{sum}}(u,u,r,s;k,2)$, establish exact one-/two-term reductions of the raw Appendix sum, the resulting factorial-canceled values, and invalid-channel vanishing. The sum retains the Appendix prefactor when reconstructed as the full Tet.
--
--   1. If $u,v>0$ and $(u,v,k)$ is admissible, put $m=(u+v+k)/2$. The raw summand for $\operatorname{Tet}^{\mathrm{sum}}(u,u,v,v;k,2)$ can be nonzero only at $m,m+1$, and its full coarse sum equals the sum of those two candidate terms. A candidate term may vanish at a boundary. The full Tet satisfies
--   $$[u][v]\operatorname{Tet}^{\mathrm{sum}}(u,u,v,v;k,2)=\theta(u,v,k)\Lambda(u,v,k).$$
--   2. If $u>0$, $(u,r,k)$ and $(u,s,k)$ are admissible, and $r=s+2$ or $s=r+2$, put $m=(u+\min(r,s)+k)/2$. The raw summand can be nonzero only at $m+1$, and its full coarse sum is that single term. In both orientations,
--   $$[u]\operatorname{Tet}^{\mathrm{sum}}(u,u,r,s;k,2)=[(u+k-\min(r,s))/2]\,\theta(\max(r,s),u,k).$$
--   3. For arbitrary integer $u,r,s,k$, the Tet is zero if any of $(u,u,2)$, $(r,s,2)$, $(u,r,k)$ or $(u,s,k)$ is inadmissible.
--
--   The coarse upper endpoints are respectively $2u+2v+k+2$ and $2u+r+s+k+2$. These statements cover the patterns $(a,a,b,b;l,2)$, $(a,a,j',j;d,2)$ and $(b,b,j',j;c,2)$ used in the rung and matrix calculations. There is no categorical seed assumption in this scalar theorem.
--
--   ### Independent mathematical read-back
--
--   # Two special tetrahedral evaluations
--
--   All labels and summation indices are integers. Work in \(\mathbb Q(q)\), with \(q\) indeterminate, and write
--   \[
--   [n]=(q^n-q^{-n})/(q-q^{-1}),\qquad
--   [n]!=\begin{cases}\prod_{i=1}^n[i],&n\ge0,\\0,&n<0.\end{cases}
--   \]
--   The empty product is one, and division by zero in this field is assigned zero. Thus a negative factorial argument in a denominator kills that term. No numerical specialization of \(q\) is asserted.
--
--   A triple is admissible if its entries are nonnegative integers satisfying all three triangle inequalities and having even sum. For an admissible triple define, with \(s=(a+b+c)/2\),
--   \[
--   \theta(a,b,c)=(-1)^s\frac{[s+1]![s-a]![s-b]![s-c]!}{[a]![b]![c]!},
--   \quad
--   \Lambda(a,b,c)=\frac{[(a-b+c)/2][(-a+b+c)/2]-[(a+b-c)/2][(a+b+c)/2+2]}{[2]}.
--   \]
--   Both functions are zero on inadmissible triples. Integer divisions mean integer division; the admissibility hypotheses make all half-sums used in the evaluations integral.
--
--   For six labels let
--   \[
--   A=\left(\frac{a+d+j}{2},\frac{b+c+j}{2},\frac{a+b+l}{2},\frac{c+d+l}{2}\right),\quad
--   B=\left(\frac{b+d+j+l}{2},\frac{a+c+j+l}{2},\frac{a+b+c+d}{2}\right),
--   \]
--   \[
--   F_{abcdjl}(z)=\frac{(-1)^z[z+1]!}{\prod_{i=0}^3[z-A_i]!\prod_{t=0}^2[B_t-z]!},\qquad
--   P_{abcdjl}=\frac{\prod_{i=0}^3\prod_{t=0}^2[B_t-A_i]!}{[a]![b]![c]![d]![j]![l]!}.
--   \]
--   The **full tetrahedral scalar** is
--   \[
--   T(a,b,c,d,j,l)=P_{abcdjl}\sum_{z=0}^{a+b+c+d+j+l}F_{abcdjl}(z)
--   \]
--   when all four triples \((a,d,j),(b,c,j),(a,b,l),(c,d,l)\) are admissible, and is zero otherwise. Sums are over inclusive integer intervals; an interval with upper endpoint below zero is empty. The raw sum and the full scalar, which includes \(P\), must be distinguished.
--
--   The assertion has five conjuncts.
--
--   ## 1. Diagonal raw-sum reduction
--
--   For every \(u,v,k\in\mathbb Z\), assume **\(u>0\), \(v>0\), and \((u,v,k)\) admissible**, and set \(m=(u+v+k)/2\). For every integer \(z\),
--   \[
--   F_{uuvvk2}(z)\ne0\ \Longrightarrow\ z=m\text{ or }z=m+1.
--   \]
--   Moreover,
--   \[
--   \sum_{z=0}^{2u+2v+k+2}F_{uuvvk2}(z)=F_{uuvvk2}(m)+F_{uuvvk2}(m+1).
--   \]
--   This reduces the **raw sum**, not the full \(T\). The two indices are candidates: the statement does not assert that both terms are nonzero. Substitution gives \(A=(m,m,u+1,v+1)\), \(B=(m+1,m+1,u+v)\), and the individual candidate terms are
--   \[
--   F_{uuvvk2}(m)=\frac{(-1)^m[m+1]!}{[m-u-1]![m-v-1]![u+v-m]!},
--   \]
--   \[
--   F_{uuvvk2}(m+1)=\frac{(-1)^{m+1}[m+2]!}{[m-u]![m-v]![u+v-m-1]!}.
--   \]
--   The same negative-factorial and total-division conventions apply to these expressions, including triangle-equality boundaries.
--
--   ## 2. Adjacent raw-sum reduction
--
--   For every \(u,r,s,k\in\mathbb Z\), assume **\(u>0\), \((u,r,k)\) and \((u,s,k)\) admissible, and either \(r=s+2\) or \(s=r+2\)**. Put \(t=\min(r,s)\) and \(m=(u+t+k)/2\). For every integer \(z\),
--   \[
--   F_{uursk2}(z)\ne0\ \Longrightarrow\ z=m+1,
--   \]
--   and
--   \[
--   \sum_{z=0}^{2u+r+s+k+2}F_{uursk2}(z)=F_{uursk2}(m+1).
--   \]
--   Again this is a statement about the **raw sum**. Up to ordering, \(A=(m,m+1,u+1,t+2)\) and \(B=(m+1,m+2,u+t+1)\). Consequently the candidate term is
--   \[
--   F_{uursk2}(m+1)=\frac{(-1)^{m+1}[m+2]!}{[m-u]![m-t-1]![u+t-m]!}.
--   \]
--   The hypotheses do not require \(r>0\) or \(s>0\) separately; their nonnegativity follows from admissibility.
--
--   ## 3. Diagonal full-scalar evaluation
--
--   For every integer \(u,v,k\) under exactly the hypotheses in part 1,
--   \[
--   [u][v]T(u,u,v,v,k,2)=\theta(u,v,k)\Lambda(u,v,k).
--   \]
--   Thus the factorial-canceled **full** scalar is
--   \[
--   T(u,u,v,v,k,2)=\frac{\theta(u,v,k)}{[u][v][2]}
--   \left([(u-v+k)/2][(-u+v+k)/2]-[(u+v-k)/2][(u+v+k)/2+2]\right).
--   \]
--   Here \([u]\) and \([v]\) are nonzero for positive \(u,v\). This is not an evaluation of the raw sum without its prefactor, and the expression can vanish through cancellation even when the triples are admissible.
--
--   ## 4. Adjacent full-scalar evaluation
--
--   For every integer \(u,r,s,k\) under exactly the hypotheses in part 2,
--   \[
--   [u]T(u,u,r,s,k,2)=[(u+k-\min(r,s))/2]\,\theta(\max(r,s),u,k).
--   \]
--   Equivalently, the factorial-canceled **full** scalar is the right-hand side divided by \([u]\). The larger of \(r,s\), not the smaller, is the first theta argument; the bracket uses the smaller. Both orientations of the adjacent pair are included.
--
--   ## 5. Inadmissible zero cases
--
--   For **every** \(u,r,s,k\in\mathbb Z\), without positivity assumptions, if at least one of
--   \[
--   (u,u,2),\quad(r,s,2),\quad(u,r,k),\quad(u,s,k)
--   \]
--   is inadmissible, then \(T(u,u,r,s,k,2)=0\). This is a statement about the full scalar, not a claim that every raw summand vanishes for arbitrary inadmissible labels. In particular it covers \(u\le0\), negative labels, triangle or parity failures, and pairs \(r,s\) that fail the triple condition with 2. It does not assert that every admissible case is nonzero, nor supply a full-scalar evaluation for the other admissible label patterns not covered by parts 3 and 4.
-- source:
--   I. Khavkine, Recurrence relation for the 6j-symbol of su_q(2) as a symmetric eigenvalue problem, International Journal of Geometric Methods in Modern Physics (2015), https://doi.org/10.1142/S0219887815501170; https://arxiv.org/abs/1009.2261. Eqs. (15), (17), special last-slot-2 Tet values, derived from the Appendix finite sum.

import Definitions.Def_QuantumSixJScalar

open scoped BigOperators QuantumSixJ

namespace QuantumSixJ

theorem tet_two_evaluations :
    (∀ u v k : ℤ, 0 < u → 0 < v → Admissible u v k →
      let m := (u + v + k) / 2
      (∀ z : ℤ, tetSummand u u v v k 2 z ≠ 0 → z = m ∨ z = m + 1) ∧
      (∑ z ∈ Finset.Icc 0 (2 * u + 2 * v + k + 2), tetSummand u u v v k 2 z) =
        tetSummand u u v v k 2 m + tetSummand u u v v k 2 (m + 1)) ∧
    (∀ u r s k : ℤ, 0 < u → Admissible u r k → Admissible u s k →
      (r = s + 2 ∨ s = r + 2) →
      let m := (u + min r s + k) / 2
      (∀ z : ℤ, tetSummand u u r s k 2 z ≠ 0 → z = m + 1) ∧
      (∑ z ∈ Finset.Icc 0 (2 * u + r + s + k + 2), tetSummand u u r s k 2 z) =
        tetSummand u u r s k 2 (m + 1)) ∧
    (∀ u v k : ℤ, 0 < u → 0 < v → Admissible u v k →
      ⟬u⟭ * ⟬v⟭ * tetSum u u v v k 2 = θ u v k * Λ u v k) ∧
    (∀ u r s k : ℤ, 0 < u → Admissible u r k → Admissible u s k →
      (r = s + 2 ∨ s = r + 2) →
      ⟬u⟭ * tetSum u u r s k 2 = ⟬(u + k - min r s) / 2⟭ * θ (max r s) u k) ∧
    (∀ u r s k : ℤ,
      (¬ Admissible u u 2 ∨ ¬ Admissible r s 2 ∨
        ¬ Admissible u r k ∨ ¬ Admissible u s k) → tetSum u u r s k 2 = 0) := by sorry

end QuantumSixJ
