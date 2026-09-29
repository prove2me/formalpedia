-- Prove2me | Theorems.Thm_TateCurve_ks17_C3_exports
-- name    : TateCurve.ks17_C3_exports
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/5941323a-0ee6-59f5-a0cd-48df38040194
-- title:
--   Tate-curve keystone: collapse of bilinear sums into coefficient lines
-- statement:
--   The declaration is a single conjunction of fifteen independently quantified statements, each of which is a regrouping identity for the $q$-expansion bookkeeping of the Tate parametrisation. Throughout, $K$ denotes a nontrivially normed field with ultrametric norm which is complete (each conjunct carries its own such field), and the following abbreviations are used. For $u \in K$ and $a \in \mathbb{Z}$, `Fz u a` $= u^{a} + u^{-a} - 2$, written $F(u,a)$ below; for $m \in \mathbb{N}$, `tent u m` $= u\bigl(\sum_{i<m} u^{i}\bigr)^{2}(u^{m})^{-1}$; for $d \in \mathbb{N}$, `xDivTerm u d` $= d\,(u^{d} + (u^{-1})^{d} - 2)$ and `xCoeff u N` $= \sum_{d \mid N}$ `xDivTerm u d`; `xfun w` $= w/(1-w)^{2}$; `xCoeffFull u` is the sequence with value `xfun u` at $0$ and `xCoeff u (N+1)` at $N+1$; the truncated Cauchy products are `cauchyMulInt c d N` $= \sum_{i=1}^{N-1} c_i\, d_{N-i}$ and `cauchyMulIntTriple c d e N` $= \sum_{i=1}^{N-1} c_i \cdot$ `cauchyMulInt d e (N-i)`, all subtractions of natural numbers being truncated; `Sols N` is the finite set of quadruples $(x_1,x_2,x_3,x_4) \in \{1,\dots,N\}^{4}$ with $x_1x_2 + x_3x_4 = N$; `Finset.sigma` forms the dependent sum of finite sets; $|\cdot|$ denotes `Int.natAbs`; and `a₄Coeff` is a sequence $\mathbb{N} \to K$, entering only by name as the left factor of a Cauchy product in conjunct (12).
--
--   (1) For every additive commutative monoid $\beta$, every finite set $S \subseteq \mathbb{N}$, every $T : \mathbb{N} \to$ `Finset ℕ`, every $U : \mathbb{N} \to \mathbb{N} \to$ `Finset ℕ` and every $f : \mathbb{N} \to \mathbb{N} \to \mathbb{N} \to \beta$, the triply nested sum $\sum_{d \in S}\sum_{j \in T d}\sum_{l \in U d j} f\,d\,j\,l$ equals the single sum of $f\,q_{1,1}\,q_{1,2}\,q_2$ over $q$ in the iterated dependent sum $(S.\mathrm{sigma}\,T).\mathrm{sigma}\,(p \mapsto U\,p_1\,p_2)$.
--
--   (2) For $u, v \in K$, a type $\alpha$, a finite set $S \subseteq \alpha$, weights $w : \alpha \to K$, functions $g, h : \alpha \to \mathbb{N}$ and $N \in \mathbb{N}$ subject to the bounding hypotheses `hg` ($g\,x \le N$ for all $x \in S$) and `hh` ($h\,x \le N$ for all $x \in S$): $\sum_{x \in S} w\,x \cdot F(u, g\,x) \cdot F(v, h\,x) = \sum_{k=1}^{N}\sum_{j=1}^{N}\bigl(\sum_{x \in S,\ g\,x = k,\ h\,x = j} w\,x\bigr) F(u,k)F(v,j)$, the arguments of $F$ on the left being the integer casts of $g\,x$ and $h\,x$.
--
--   (3) The same with $g : \alpha \to \mathbb{N}$ and $h : \alpha \to \mathbb{Z}$, the hypotheses `hg` and `hh` requiring $g\,x \le N$ and $|h\,x| \le N$ for $x \in S$: $\sum_{x \in S} w\,x \cdot F(u, g\,x) \cdot F(v, h\,x) = \sum_{k=1}^{N}\sum_{j=1}^{N}\bigl(\sum_{x \in S,\ g\,x = k,\ |h\,x| = j} w\,x\bigr) F(u,k)F(v,j)$.
--
--   (4) The mirror image of (3), with $g : \alpha \to \mathbb{Z}$ and $h : \alpha \to \mathbb{N}$, hypotheses `hg` ($|g\,x| \le N$) and `hh` ($h\,x \le N$) for $x \in S$, and the filter $|g\,x| = k$, $h\,x = j$.
--
--   (5) The case of two integer-valued functions $g, h : \alpha \to \mathbb{Z}$, with hypotheses `hg` ($|g\,x| \le N$) and `hh` ($|h\,x| \le N$) for $x \in S$: $\sum_{x \in S} w\,x \cdot F(u, g\,x)\cdot F(v, h\,x) = \sum_{k=1}^{N}\sum_{j=1}^{N}\bigl(\sum_{x \in S,\ |g\,x| = k,\ |h\,x| = j} w\,x\bigr) F(u,k)F(v,j)$.
--
--   (6) For every additive commutative monoid $\beta$, every $M \in \mathbb{N}$ and every $f : \mathbb{N} \to \mathbb{N} \to (\mathbb{N}\times\mathbb{N}\times\mathbb{N}\times\mathbb{N}) \to \beta$, the nested sum $\sum_{i=1}^{M-1}\sum_{d \mid i}\sum_{x \in \mathrm{Sols}(M-i)} f\,i\,d\,x$ equals the sum of $f\,q_{1,1}\,q_{1,2}\,q_2$ over the iterated dependent sum $\bigl((\mathrm{Ico}\,1\,M).\mathrm{sigma}\,(i \mapsto i.\mathrm{divisors})\bigr).\mathrm{sigma}\,(p \mapsto \mathrm{Sols}(M - p_1))$.
--
--   (7) For $u \in K$ with $K$ of characteristic zero, hypotheses `hu0` ($u \neq 0$) and `hu1` ($u \neq 1$), and arbitrary $v \in K$, $M \in \mathbb{N}$:
--   $$\sum_{x \in \mathrm{Sols}\,M} x_1 \cdot \mathrm{tent}(u, x_1)\cdot \mathrm{xDivTerm}(v, x_3) = \sum_{j=1}^{M}\Bigl(\sum_{x \in \mathrm{Sols}\,M,\ x_3 = j} x_1^{3} x_3\Bigr) F(v,j) + \sum_{k=1}^{M}\sum_{j=1}^{M}\Bigl(\sum_{p} x_1 (x_1 - p_2) x_3\Bigr) F(u,k)F(v,j),$$
--   where the inner sum runs over the pairs $p$ of the dependent sum $(\mathrm{Sols}\,M).\mathrm{sigma}\,(x \mapsto \mathrm{Ico}\,1\,x_1)$, with $x = p_1$, satisfying $p_2 = k$ and $x_3 = j$, and $x_1 - p_2$ is truncated natural subtraction.
--
--   (8) For $v \in K$ with $K$ of characteristic zero, hypotheses `hv0` ($v \neq 0$) and `hv1` ($v \neq 1$), and arbitrary $u \in K$, $M \in \mathbb{N}$:
--   $$\sum_{x \in \mathrm{Sols}\,M} \mathrm{xDivTerm}(u, x_1)\cdot\bigl(x_3\,\mathrm{tent}(v, x_3)\bigr) = \sum_{k=1}^{M}\Bigl(\sum_{x \in \mathrm{Sols}\,M,\ x_1 = k} x_3^{3} x_1\Bigr) F(u,k) + \sum_{k=1}^{M}\sum_{j=1}^{M}\Bigl(\sum_{p} x_3 (x_3 - p_2) x_1\Bigr) F(u,k)F(v,j),$$
--   the inner sum running over the pairs $p$ of $(\mathrm{Sols}\,M).\mathrm{sigma}\,(x \mapsto \mathrm{Ico}\,1\,x_3)$ with $x_1 = k$ and $p_2 = j$.
--
--   (9) For $u \in K$ with hypothesis `hu0` ($u \neq 0$), arbitrary $v \in K$ and $M \in \mathbb{N}$, writing $Q_M$ for the index set $\bigl((\mathrm{Ico}\,1\,M).\mathrm{sigma}\,(i \mapsto i.\mathrm{divisors})\bigr).\mathrm{sigma}\,(p \mapsto \mathrm{Sols}(M-p_1))$, whose elements $q$ consist of $i$, a divisor $d = q_{1,2}$ of $i$, and a quadruple $x \in \mathrm{Sols}(M-i)$, the quantity `cauchyMulIntTriple (xCoeffFull u) (xCoeffFull u) (xCoeffFull v) M` equals
--   $$\sum_{k=1}^{M}\sum_{j=1}^{M} C_{|d + x_1| = k,\ x_3 = j}\,F(u,k)F(v,j) + \sum_{k,j} C_{|d - x_1| = k,\ x_3 = j}\,F(u,k)F(v,j) - 2\sum_{k,j} C_{d = k,\ x_3 = j}\,F(u,k)F(v,j) - 2\sum_{k,j} C_{x_1 = k,\ x_3 = j}\,F(u,k)F(v,j),$$
--   where $C_{\text{condition}}$ denotes the sum of $d\,x_1\,x_3$ over the elements of $Q_M$ satisfying the indicated condition, the sums $d \pm x_1$ being formed in $\mathbb{Z}$.
--
--   (10) For $v \in K$ with hypothesis `hv0` ($v \neq 0$), arbitrary $u \in K$ and $M \in \mathbb{N}$, with $Q_M$ and $C$ as in (9), the quantity `cauchyMulIntTriple (xCoeffFull u) (xCoeffFull v) (xCoeffFull v) M` equals
--   $$\sum_{k,j=1}^{M} C_{d = k,\ |x_1 + x_3| = j}F(u,k)F(v,j) + \sum_{k,j} C_{d = k,\ |x_1 - x_3| = j}F(u,k)F(v,j) - 2\sum_{k,j} C_{d = k,\ x_1 = j}F(u,k)F(v,j) - 2\sum_{k,j} C_{d = k,\ x_3 = j}F(u,k)F(v,j).$$
--
--   (11) For arbitrary $u, v \in K$ and $M \in \mathbb{N}$: `cauchyMulInt (xCoeffFull u) (xCoeffFull v) M` $= \sum_{k=1}^{M}\sum_{j=1}^{M}\bigl(\sum_{x \in \mathrm{Sols}\,M,\ x_1 = k,\ x_3 = j} x_1 x_3\bigr) F(u,k)F(v,j)$.
--
--   (12) For arbitrary $u \in K$ and $M \in \mathbb{N}$: `cauchyMulInt a₄Coeff (xCoeffFull u) M` $= \sum_{k=1}^{M}\bigl(\sum_{x \in \mathrm{Sols}\,M,\ x_3 = k} -\,(5x_1^{3})\,x_3\bigr) F(u,k)$, the factor $5x_1^{3}$ being computed in $\mathbb{N}$ and then cast to $K$.
--
--   (13) For arbitrary $u, v \in K$ and $M \in \mathbb{N}$, let $R_M$ be the index set $\bigl((\mathrm{Sols}\,M).\mathrm{sigma}\,(x \mapsto \mathrm{range}\,x_1)\bigr).\mathrm{sigma}\,(p \mapsto \mathrm{range}\,(p_1)_3)$, whose elements $q$ consist of $x \in \mathrm{Sols}\,M$, an index $i < x_1$ and an index $i' < x_3$, and let $D_{\text{condition}}$ denote the sum of $x_1 x_3$ over the elements of $R_M$ satisfying the condition. Then
--   $$\sum_{x \in \mathrm{Sols}\,M}\ \sum_{i < x_1}\ \sum_{i' < x_3} x_1 x_3\Bigl(F(u, i+i'+1)F(v, x_1+x_3-1-i-i') - F(u, i+i'+1-x_3)F(v, i+i'+1-x_1) + 2\bigl(F(u,i+i'+1) - F(u, i+i'+1-x_3)\bigr) + 2\bigl(F(v, x_1+x_3-1-i-i') - F(v, i+i'+1-x_1)\bigr)\Bigr)$$
--   (all arguments of $F$ formed in $\mathbb{Z}$) equals
--   $$\sum_{k,j=1}^{M} D_{|i+i'+1| = k,\ |x_1+x_3-1-i-i'| = j}F(u,k)F(v,j) - \sum_{k,j=1}^{M} D_{|i+i'+1-x_3| = k,\ |i+i'+1-x_1| = j}F(u,k)F(v,j) + 2\sum_{k=1}^{M} D_{|i+i'+1| = k}F(u,k) - 2\sum_{k=1}^{M} D_{|i+i'+1-x_3| = k}F(u,k) + 2\sum_{j=1}^{M} D_{|x_1+x_3-1-i-i'| = j}F(v,j) - 2\sum_{j=1}^{M} D_{|i+i'+1-x_1| = j}F(v,j).$$
--
--   (14) For arbitrary $u, v \in K$ and $M \in \mathbb{N}$, an identity between a divisor sum and its line expansion. On the left stands $\sum_{d \mid M} d\,(A_d - B_d)$, where
--   $$A_d = \sum_{j=1}^{d}\Bigl(j^{2}(d+1-j)^{2} + j^{2}\!\!\sum_{l=1}^{d-j}(d+1-j-l)F(u,l) + (d+1-j)^{2}\!\!\sum_{l=1}^{j-1}(j-l)F(v,l) + \sum_{l=1}^{j-1}\sum_{l'=1}^{d-j}(j-l)(d+1-j-l')F(v,l)F(u,l')\Bigr)$$
--   and $B_d$ is the sum of the same four expressions with $d+1-j$ replaced throughout by $d-1-j$ and with $j$ running over $0 \le j < d$; all subtractions of natural numbers are truncated and the ranges of $l$ and $l'$ are the corresponding intervals $\mathrm{Ico}\,1\,(\cdot)$. On the right stands the difference of two groups of four terms. The first group, attached to the index sets built from $M.\mathrm{divisors}.\mathrm{sigma}\,(d \mapsto \mathrm{Icc}\,1\,d)$, consists of: $\sum_{d \mid M}\sum_{j=1}^{d} d\,j^{2}(d+1-j)^{2}$; the $u$-line $\sum_{k=1}^{M}\bigl(\sum_{q} d\,j^{2}(d+1-j-l)\bigr)F(u,k)$ over the triples $q = ((d,j),l)$ of $\bigl(M.\mathrm{divisors}.\mathrm{sigma}(d \mapsto \mathrm{Icc}\,1\,d)\bigr).\mathrm{sigma}\,(p \mapsto \mathrm{Ico}\,1\,(p_1+1-p_2))$ with $l = k$; the $v$-line $\sum_{j=1}^{M}\bigl(\sum_{q} d\,(d+1-j')^{2}(j'-l)\bigr)F(v,j)$ over the triples $q = ((d,j'),l)$ of $\bigl(M.\mathrm{divisors}.\mathrm{sigma}(d \mapsto \mathrm{Icc}\,1\,d)\bigr).\mathrm{sigma}\,(p \mapsto \mathrm{Ico}\,1\,p_2)$ with $l = j$; and the bilinear lines $\sum_{k,j=1}^{M}\bigl(\sum_{q} d\,(j'-l)(d+1-j'-l')\bigr)F(u,k)F(v,j)$ over the quadruples $q = (((d,j'),l),l')$ of $\bigl(\bigl(M.\mathrm{divisors}.\mathrm{sigma}(d \mapsto \mathrm{Icc}\,1\,d)\bigr).\mathrm{sigma}(p \mapsto \mathrm{Ico}\,1\,p_2)\bigr).\mathrm{sigma}\,(r \mapsto \mathrm{Ico}\,1\,(r_{1,1}+1-r_{1,2}))$ with $l' = k$ and $l = j$. The second group is the exact analogue with $\mathrm{Icc}\,1\,d$ replaced by $\mathrm{range}\,d$ and each occurrence of $d+1-(\cdot)$ replaced by $d-1-(\cdot)$.
--
--   (15) For $u, v \in K$ with hypotheses `hu0` ($u \neq 0$) and `hv0` ($v \neq 0$), and $M \in \mathbb{N}$:
--   $$\sum_{a=1}^{M-1}\bigl(\mathrm{xCoeff}(uv, a) + \mathrm{xCoeff}(uv^{-1}, a)\bigr)\cdot \mathrm{cauchyMulInt}\,\bigl(i \mapsto \mathrm{xCoeffFull}(u,i) - \mathrm{xCoeffFull}(v,i)\bigr)\bigl(i \mapsto \mathrm{xCoeffFull}(u,i) - \mathrm{xCoeffFull}(v,i)\bigr)(M-a)$$
--   equals
--   $$\sum_{a=1}^{M-1}\ \sum_{d \mid a}\ \sum_{x \in \mathrm{Sols}(M-a)} d\,x_1\,x_3\bigl(F(u,d)F(v,d) + 2F(u,d) + 2F(v,d)\bigr)\bigl((F(u,x_1) - F(v,x_1))(F(u,x_3) - F(v,x_3))\bigr).$$
--
--   These fifteen identities form the first collapse layer of the $q$-expansion verification that the Tate parametrisation of $y^2 + xy = x^3 + a_4(q)x + a_6(q)$ satisfies the symmetric addition identities: the generic Fubini-type regroupings (1)–(6) and the regroupings (7)–(15) of the Cauchy products of the coefficient sequences `xCoeffFull`, `xCoeff` and `a₄Coeff` into coefficient lines $\sum_{k,j}(\cdot)F(u,k)F(v,j)$ indexed by the divisor-convolution solution sets `Sols`. Packaged as a conjunction so that later stages can use each part separately, it is cited by [`TateCurve.symAdd_sum_regional`](thm.html#TateCurve.symAdd_sum_regional), [`TateCurve.diffHyp_unconditional`](thm.html#TateCurve.diffHyp_unconditional) and [`TateCurve.ks17_D3_exports`](thm.html#TateCurve.ks17_D3_exports).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TateCurve_ks17_C3_exports.lean

import Mathlib
import Definitions.Def_TateCurve_XMultIdentities
import Definitions.Def_TateCurve_KeystoneVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped NNReal
open TateCurve FLT.DivisorConvolution FLT.DivisorConvolution.BesgeCertificate Finset

theorem TateCurve.ks17_C3_exports.{u_1, u_2} :

    (∀ {β : Type u_2} [AddCommMonoid β] (S : Finset ℕ) (T : ℕ → Finset ℕ)
    (U : ℕ → ℕ → Finset ℕ) (f : ℕ → ℕ → ℕ → β),
      ∑ d ∈ S, ∑ j ∈ T d, ∑ l ∈ U d j, f d j l = ∑ q ∈ (S.sigma T).sigma fun p => U p.1 p.2, f q.1.1 q.1.2 q.2) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} {α : Type u_2} (S : Finset α) (w : α → K) (g h : α → ℕ)
    {N : ℕ} (hg : ∀ x ∈ S, g x ≤ N) (hh : ∀ x ∈ S, h x ≤ N),
      ∑ x ∈ S, w x * Fz u (g x : ℤ) * Fz v (h x : ℤ) = ∑ k ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N, (∑ x ∈ S.filter (fun x => g x = k ∧ h x = j), w x) * Fz u (k : ℤ) * Fz v (j : ℤ)) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} {α : Type u_2} (S : Finset α) (w : α → K) (g : α → ℕ)
    (h : α → ℤ) {N : ℕ} (hg : ∀ x ∈ S, g x ≤ N) (hh : ∀ x ∈ S, (h x).natAbs ≤ N),
      ∑ x ∈ S, w x * Fz u (g x : ℤ) * Fz v (h x) = ∑ k ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N, (∑ x ∈ S.filter (fun x => g x = k ∧ (h x).natAbs = j), w x) * Fz u (k : ℤ) * Fz v (j : ℤ)) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} {α : Type u_2} (S : Finset α) (w : α → K) (g : α → ℤ)
    (h : α → ℕ) {N : ℕ} (hg : ∀ x ∈ S, (g x).natAbs ≤ N) (hh : ∀ x ∈ S, h x ≤ N),
      ∑ x ∈ S, w x * Fz u (g x) * Fz v (h x : ℤ) = ∑ k ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N, (∑ x ∈ S.filter (fun x => (g x).natAbs = k ∧ h x = j), w x) * Fz u (k : ℤ) * Fz v (j : ℤ)) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} {α : Type u_2} (S : Finset α) (w : α → K) (g h : α → ℤ)
    {N : ℕ} (hg : ∀ x ∈ S, (g x).natAbs ≤ N) (hh : ∀ x ∈ S, (h x).natAbs ≤ N),
      ∑ x ∈ S, w x * Fz u (g x) * Fz v (h x) = ∑ k ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N, (∑ x ∈ S.filter (fun x => (g x).natAbs = k ∧ (h x).natAbs = j), w x) * Fz u (k : ℤ) * Fz v (j : ℤ)) ∧

    (∀ {β : Type u_2} [AddCommMonoid β] (M : ℕ)
    (f : ℕ → ℕ → ℕ × ℕ × ℕ × ℕ → β),
      ∑ i ∈ Finset.Ico 1 M, ∑ d ∈ i.divisors, ∑ x ∈ Sols (M - i), f i d x = ∑ q ∈ ((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1), f q.1.1 q.1.2 q.2) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u : K} [CharZero K] (hu0 : u ≠ 0) (hu1 : u ≠ 1) (v : K) (M : ℕ),
      ∑ x ∈ Sols M, (x.1 : K) * tent u x.1 * xDivTerm v x.2.2.1 = (∑ j ∈ Finset.Icc 1 M, (∑ x ∈ (Sols M).filter (fun x => x.2.2.1 = j), (x.1 : K) ^ 3 * (x.2.2.1 : K)) * Fz v (j : ℤ)) + ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ p ∈ ((Sols M).sigma fun x => Finset.Ico 1 x.1).filter (fun p => p.2 = k ∧ p.1.2.2.1 = j), (p.1.1 : K) * ((p.1.1 - p.2 : ℕ) : K) * (p.1.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {v : K} [CharZero K] (u : K) (hv0 : v ≠ 0) (hv1 : v ≠ 1) (M : ℕ),
      ∑ x ∈ Sols M, xDivTerm u x.1 * ((x.2.2.1 : K) * tent v x.2.2.1) = (∑ k ∈ Finset.Icc 1 M, (∑ x ∈ (Sols M).filter (fun x => x.1 = k), (x.2.2.1 : K) ^ 3 * (x.1 : K)) * Fz u (k : ℤ)) + ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ p ∈ ((Sols M).sigma fun x => Finset.Ico 1 x.2.2.1).filter (fun p => p.1.1 = k ∧ p.2 = j), (p.1.2.2.1 : K) * ((p.1.2.2.1 - p.2 : ℕ) : K) * (p.1.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u : K} (hu0 : u ≠ 0) (v : K) (M : ℕ),
      cauchyMulIntTriple (xCoeffFull u) (xCoeffFull u) (xCoeffFull v) M = (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => ((q.1.2 : ℤ) + (q.2.1 : ℤ)).natAbs = k ∧ q.2.2.2.1 = j), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) + (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => ((q.1.2 : ℤ) - (q.2.1 : ℤ)).natAbs = k ∧ q.2.2.2.1 = j), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) - 2 * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => q.1.2 = k ∧ q.2.2.2.1 = j), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) - 2 * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => q.2.1 = k ∧ q.2.2.2.1 = j), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ))) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {v : K} (u : K) (hv0 : v ≠ 0) (M : ℕ),
      cauchyMulIntTriple (xCoeffFull u) (xCoeffFull v) (xCoeffFull v) M = (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => q.1.2 = k ∧ ((q.2.1 : ℤ) + (q.2.2.2.1 : ℤ)).natAbs = j), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) + (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => q.1.2 = k ∧ ((q.2.1 : ℤ) - (q.2.2.2.1 : ℤ)).natAbs = j), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) - 2 * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => q.1.2 = k ∧ q.2.1 = j), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) - 2 * (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Finset.Ico 1 M).sigma fun i => i.divisors).sigma fun p => Sols (M - p.1)).filter (fun q => q.1.2 = k ∧ q.2.2.2.1 = j), (q.1.2 : K) * (q.2.1 : K) * (q.2.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ))) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] (u v : K) (M : ℕ),
      cauchyMulInt (xCoeffFull u) (xCoeffFull v) M = ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ x ∈ (Sols M).filter (fun x => x.1 = k ∧ x.2.2.1 = j), (x.1 : K) * (x.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] (u : K) (M : ℕ),
      cauchyMulInt a₄Coeff (xCoeffFull u) M = ∑ k ∈ Finset.Icc 1 M, (∑ x ∈ (Sols M).filter (fun x => x.2.2.1 = k), -((5 * x.1 ^ 3 : ℕ) : K) * (x.2.2.1 : K)) * Fz u (k : ℤ)) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] (u v : K) (M : ℕ),
      ∑ x ∈ Sols M, ∑ i ∈ Finset.range x.1, ∑ i' ∈ Finset.range x.2.2.1, (x.1 : K) * (x.2.2.1 : K) * (Fz u ((i : ℤ) + i' + 1) * Fz v ((x.1 : ℤ) + x.2.2.1 - 1 - i - i') - Fz u ((i : ℤ) + i' + 1 - x.2.2.1) * Fz v ((i : ℤ) + i' + 1 - x.1) + 2 * (Fz u ((i : ℤ) + i' + 1) - Fz u ((i : ℤ) + i' + 1 - x.2.2.1)) + 2 * (Fz v ((x.1 : ℤ) + x.2.2.1 - 1 - i - i') - Fz v ((i : ℤ) + i' + 1 - x.1))) = (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Sols M).sigma fun x => Finset.range x.1).sigma fun p => Finset.range p.1.2.2.1).filter (fun q => ((q.1.2 : ℤ) + q.2 + 1).natAbs = k ∧ ((q.1.1.1 : ℤ) + q.1.1.2.2.1 - 1 - q.1.2 - q.2).natAbs = j), (q.1.1.1 : K) * (q.1.1.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) - (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Sols M).sigma fun x => Finset.range x.1).sigma fun p => Finset.range p.1.2.2.1).filter (fun q => ((q.1.2 : ℤ) + q.2 + 1 - q.1.1.2.2.1).natAbs = k ∧ ((q.1.2 : ℤ) + q.2 + 1 - q.1.1.1).natAbs = j), (q.1.1.1 : K) * (q.1.1.2.2.1 : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)) + 2 * (∑ k ∈ Finset.Icc 1 M, (∑ q ∈ (((Sols M).sigma fun x => Finset.range x.1).sigma fun p => Finset.range p.1.2.2.1).filter (fun q => ((q.1.2 : ℤ) + q.2 + 1).natAbs = k), (q.1.1.1 : K) * (q.1.1.2.2.1 : K)) * Fz u (k : ℤ)) - 2 * (∑ k ∈ Finset.Icc 1 M, (∑ q ∈ (((Sols M).sigma fun x => Finset.range x.1).sigma fun p => Finset.range p.1.2.2.1).filter (fun q => ((q.1.2 : ℤ) + q.2 + 1 - q.1.1.2.2.1).natAbs = k), (q.1.1.1 : K) * (q.1.1.2.2.1 : K)) * Fz u (k : ℤ)) + 2 * (∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Sols M).sigma fun x => Finset.range x.1).sigma fun p => Finset.range p.1.2.2.1).filter (fun q => ((q.1.1.1 : ℤ) + q.1.1.2.2.1 - 1 - q.1.2 - q.2).natAbs = j), (q.1.1.1 : K) * (q.1.1.2.2.1 : K)) * Fz v (j : ℤ)) - 2 * (∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((Sols M).sigma fun x => Finset.range x.1).sigma fun p => Finset.range p.1.2.2.1).filter (fun q => ((q.1.2 : ℤ) + q.2 + 1 - q.1.1.1).natAbs = j), (q.1.1.1 : K) * (q.1.1.2.2.1 : K)) * Fz v (j : ℤ))) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] (u v : K) (M : ℕ),
      ∑ d ∈ M.divisors, (d : K) * ((∑ j ∈ Finset.Icc 1 d, ((j : K) ^ 2 * ((d + 1 - j : ℕ) : K) ^ 2 + (j : K) ^ 2 * (∑ l ∈ Finset.Ico 1 (d + 1 - j), ((d + 1 - j - l : ℕ) : K) * Fz u (l : ℤ)) + ((d + 1 - j : ℕ) : K) ^ 2 * (∑ l ∈ Finset.Ico 1 j, ((j - l : ℕ) : K) * Fz v (l : ℤ)) + ∑ l ∈ Finset.Ico 1 j, ∑ l' ∈ Finset.Ico 1 (d + 1 - j), ((j - l : ℕ) : K) * ((d + 1 - j - l' : ℕ) : K) * Fz v (l : ℤ) * Fz u (l' : ℤ))) - ∑ j ∈ Finset.range d, ((j : K) ^ 2 * ((d - 1 - j : ℕ) : K) ^ 2 + (j : K) ^ 2 * (∑ l ∈ Finset.Ico 1 (d - 1 - j), ((d - 1 - j - l : ℕ) : K) * Fz u (l : ℤ)) + ((d - 1 - j : ℕ) : K) ^ 2 * (∑ l ∈ Finset.Ico 1 j, ((j - l : ℕ) : K) * Fz v (l : ℤ)) + ∑ l ∈ Finset.Ico 1 j, ∑ l' ∈ Finset.Ico 1 (d - 1 - j), ((j - l : ℕ) : K) * ((d - 1 - j - l' : ℕ) : K) * Fz v (l : ℤ) * Fz u (l' : ℤ))) = ((∑ d ∈ M.divisors, ∑ j ∈ Finset.Icc 1 d, (d : K) * ((j : K) ^ 2 * ((d + 1 - j : ℕ) : K) ^ 2)) + (∑ k ∈ Finset.Icc 1 M, (∑ q ∈ ((M.divisors.sigma fun d => Finset.Icc 1 d).sigma fun p => Finset.Ico 1 (p.1 + 1 - p.2)).filter (fun q => q.2 = k), (q.1.1 : K) * (q.1.2 : K) ^ 2 * ((q.1.1 + 1 - q.1.2 - q.2 : ℕ) : K)) * Fz u (k : ℤ)) + (∑ j ∈ Finset.Icc 1 M, (∑ q ∈ ((M.divisors.sigma fun d => Finset.Icc 1 d).sigma fun p => Finset.Ico 1 p.2).filter (fun q => q.2 = j), (q.1.1 : K) * ((q.1.1 + 1 - q.1.2 : ℕ) : K) ^ 2 * ((q.1.2 - q.2 : ℕ) : K)) * Fz v (j : ℤ)) + (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((M.divisors.sigma fun d => Finset.Icc 1 d).sigma fun p => Finset.Ico 1 p.2).sigma fun r => Finset.Ico 1 (r.1.1 + 1 - r.1.2)).filter (fun q => q.2 = k ∧ q.1.2 = j), (q.1.1.1 : K) * ((q.1.1.2 - q.1.2 : ℕ) : K) * ((q.1.1.1 + 1 - q.1.1.2 - q.2 : ℕ) : K)) * Fz u (k : ℤ) * Fz v (j : ℤ))) - ((∑ d ∈ M.divisors, ∑ j ∈ Finset.range d, (d : K) * ((j : K) ^ 2 * ((d - 1 - j : ℕ) : K) ^ 2)) + (∑ k ∈ Finset.Icc 1 M, (∑ q ∈ ((M.divisors.sigma fun d => Finset.range d).sigma fun p => Finset.Ico 1 (p.1 - 1 - p.2)).filter (fun q => q.2 = k), (q.1.1 : K) * (q.1.2 : K) ^ 2 * ((q.1.1 - 1 - q.1.2 - q.2 : ℕ) : K)) * Fz u (k : ℤ)) + (∑ j ∈ Finset.Icc 1 M, (∑ q ∈ ((M.divisors.sigma fun d => Finset.range d).sigma fun p => Finset.Ico 1 p.2).filter (fun q => q.2 = j), (q.1.1 : K) * ((q.1.1 - 1 - q.1.2 : ℕ) : K) ^ 2 * ((q.1.2 - q.2 : ℕ) : K)) * Fz v (j : ℤ)) + (∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (∑ q ∈ (((M.divisors.sigma fun d => Finset.range d).sigma fun p => Finset.Ico 1 p.2).sigma fun r => Finset.Ico 1 (r.1.1 - 1 - r.1.2)).filter (fun q => q.2 = k ∧ q.1.2 = j), (q.1.1.1 : K) * ((q.1.1.2 - q.1.2 : ℕ) : K) * ((q.1.1.1 - 1 - q.1.1.2 - q.2 : ℕ) : K)) * Fz u (k : ℤ) * Fz v (j : ℤ)))) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} (hu0 : u ≠ 0) (hv0 : v ≠ 0) (M : ℕ),
      ∑ a ∈ Finset.Ico 1 M, (xCoeff (u * v) a + xCoeff (u * v⁻¹) a) * cauchyMulInt (fun i => xCoeffFull u i - xCoeffFull v i) (fun i => xCoeffFull u i - xCoeffFull v i) (M - a) = ∑ a ∈ Finset.Ico 1 M, ∑ d ∈ a.divisors, ∑ x ∈ Sols (M - a), (d : K) * (x.1 : K) * (x.2.2.1 : K) * (Fz u (d : ℤ) * Fz v (d : ℤ) + 2 * Fz u (d : ℤ) + 2 * Fz v (d : ℤ)) * ((Fz u (x.1 : ℤ) - Fz v (x.1 : ℤ)) * (Fz u (x.2.2.1 : ℤ) - Fz v (x.2.2.1 : ℤ)))) := by sorry
