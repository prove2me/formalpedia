-- Prove2me | Theorems.Thm_TateCurve_ks17_C2_exports
-- name    : TateCurve.ks17_C2_exports
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/c15afe22-0d1c-52c1-977c-25d71f7fdfcd
-- title:
--   Row-form and three-bin identities for the Tate addition defect
-- statement:
--   Throughout, $K$ is a nontrivially normed field which is ultrametric and complete (in the tenth conjunct only the nontrivially normed field structure, together with characteristic zero, is assumed), $u,v\in K$ and $M,N\in\mathbb{N}$. The following abbreviations are used for the project notions occurring in the statement: $F_u(a)=u^{a}+u^{-a}-2$ for `Fz u a` ($a\in\mathbb{Z}$); $T_u(m)=u\bigl(\sum_{i<m}u^{i}\bigr)^{2}(u^{m})^{-1}$ for `tent u m`; $\Delta_u(a,c)=F_u(a+c)+F_u(a-c)-2F_u(a)-2F_u(c)$ for the second-difference combination that occurs literally in the Lean text; `xDivTerm u d` $=d\,(u^{d}+(u^{-1})^{d}-2)$ and `xCoeff u N` $=\sum_{d\mid N}$ `xDivTerm u d`; `xfun w` $=w/(1-w)^{2}$, and `xCoeffFull u` is the sequence with value `xfun u` at $0$ and `xCoeff u (N+1)` at $N+1$. Two truncated convolutions appear: `cauchyMulInt c d N` $=\sum_{i=1}^{N-1}c(i)\,d(N-i)$ and `cauchyMulIntTriple c d e N` $=\sum_{i=1}^{N-1}c(i)\,$`cauchyMulInt d e`$(N-i)$, whereas `cauchyMul c d N` is the full antidiagonal product $\sum_{k+l=N}c(k)d(l)$. The finite set `Sols M` consists of the quadruples $x=(m,m',n,n')$ with $1\le m,m',n,n'\le M$ and $mm'+nn'=M$; only the first and third components $m=x.1$ and $n=x.2.2.1$ occur in the summands below. The sequences `a₄Coeff` and `a₆Coeff` are referred to by name; they occupy, in the defect combination, the positions of the Weierstrass coefficients $a_4$ and $a_6$. All subtractions inside casts from $\mathbb{N}$ (such as $((d-k:\mathbb{N}):K)$) are truncated subtractions of naturals, performed before the cast.
--
--   The assertion is a conjunction of eighteen independently quantified identities. The hypotheses used are drawn from the groups: the non-vanishing hypotheses `hu0 : u ≠ 0`, `hv0 : v ≠ 0`; the non-triviality hypotheses `hu1 : u ≠ 1`, `hv1 : v ≠ 1`, `huvm : u * v ≠ 1`, `huvd : u * v⁻¹ ≠ 1`; the positivity hypothesis `hM : 0 < M`; and, where stated, characteristic zero for $K$. Each conjunct lists exactly those it assumes.
--
--   (1) For all $u,v$ and all $M$, with no further hypotheses,
--   $$\textstyle\sum_{i=1}^{M-1}\,(\mathrm{xCoeffFull}\ u)(i)\,(\mathrm{xCoeffFull}\ v)(M-i)=\sum_{x\in\mathrm{Sols}\,M} m\,n\,F_u(m)\,F_v(n).$$
--
--   (2) For all $u$ and all $M$, with no further hypotheses, `cauchyMulInt a₄Coeff (xCoeffFull u) M` $=-\sum_{x\in\mathrm{Sols}\,M}(5m^{3})\,\bigl(n\,F_u(n)\bigr)$, the factor $5m^{3}$ being formed in $\mathbb{N}$ and then cast.
--
--   (3) For $K$ of characteristic zero, under `hu0` and `hu1`, for all $v$ and $M$,
--   $$\textstyle\sum_{x\in\mathrm{Sols}\,M} m\,T_u(m)\,(\mathrm{xDivTerm}\ v\ n)=\sum_{x\in\mathrm{Sols}\,M} m^{3}n\,F_v(n)+\sum_{x\in\mathrm{Sols}\,M}\ \sum_{j=1}^{m-1} m\,(m-j)\,n\,F_u(j)\,F_v(n).$$
--
--   (4) For $K$ of characteristic zero, under `hv0` and `hv1`, for all $u$ and $M$,
--   $$\textstyle\sum_{x\in\mathrm{Sols}\,M}(\mathrm{xDivTerm}\ u\ m)\,\bigl(n\,T_v(n)\bigr)=\sum_{x\in\mathrm{Sols}\,M} n^{3}m\,F_u(m)+\sum_{x\in\mathrm{Sols}\,M}\ \sum_{j=1}^{n-1} n\,(n-j)\,m\,F_u(m)\,F_v(j).$$
--
--   (5) Under `hu0`, for all $v$ and $M$, `cauchyMulIntTriple (xCoeffFull u) (xCoeffFull u) (xCoeffFull v) M` equals
--   $$\textstyle\sum_{i=1}^{M-1}\ \sum_{d\mid i}\ \sum_{x\in\mathrm{Sols}(M-i)} d\,m\,n\,\bigl(F_u(d+m)+F_u(d-m)-2F_u(d)-2F_u(m)\bigr)F_v(n).$$
--
--   (6) Under `hv0`, for all $u$ and $M$, `cauchyMulIntTriple (xCoeffFull u) (xCoeffFull v) (xCoeffFull v) M` equals
--   $$\textstyle\sum_{i=1}^{M-1}\ \sum_{d\mid i}\ \sum_{x\in\mathrm{Sols}(M-i)} d\,m\,n\,F_u(d)\bigl(F_v(m+n)+F_v(m-n)-2F_v(m)-2F_v(n)\bigr).$$
--
--   (7) Under `hu0`, for all $d,a\in\mathbb{Z}$,
--   $$\bigl(F_u(d)F_v(d)+2F_u(d)+2F_v(d)\bigr)F_u(a)=F_v(d)\,\Delta_u(d,a)+2\,\Delta_u(d,a)+2F_v(d)F_u(a).$$
--
--   (8) Under `hv0`, for all $d,a\in\mathbb{Z}$, the mirror identity
--   $$\bigl(F_u(d)F_v(d)+2F_u(d)+2F_v(d)\bigr)F_v(a)=F_u(d)\,\Delta_v(d,a)+2\,\Delta_v(d,a)+2F_u(d)F_v(a).$$
--
--   (9) Under `hu0` and `hv0`, for all $a,b,c,d\in\mathbb{Z}$,
--   $$\bigl(F_u(a)F_v(b)\bigr)\bigl(F_u(c)F_v(d)\bigr)=\Delta_u(a,c)\,\Delta_v(b,d).$$
--
--   (10) For $K$ a nontrivially normed field of characteristic zero and $M>0$ (the ultrametric and completeness assumptions are not made in this conjunct),
--   $$-2\sum_{d\mid M} d\Bigl(\sum_{j=1}^{d} j^{2}(d+1-j)^{2}-\sum_{j<d} j^{2}(d-1-j)^{2}\Bigr)+\sum_{d\mid M} d\Bigl(2\sum_{k=1}^{d-1}(d-k)k^{2}+2\sum_{k=1}^{d-1}(d-k)k^{2}-2\,d^{2}d^{2}\Bigr)-4\,(\mathrm{a₆Coeff}\ M)=0 .$$
--
--   (11) Under `hu0` and `hv0`, for all $M$, the closed-form sum
--   $$\sum_{x\in\mathrm{Sols}\,M} m\,n\Bigl[(u^{m}-v^{m})(u^{n}-v^{n})\,\bigl(uv\,\textstyle\sum_{i<m}(uv)^{i}\sum_{i<n}(uv)^{i}\,((uv)^{m})^{-1}((uv)^{n})^{-1}\bigr)+\bigl(u^{m}-(v^{m})^{-1}\bigr)\bigl(u^{n}-(v^{n})^{-1}\bigr)\bigl(uv^{-1}\textstyle\sum_{i<m}(uv^{-1})^{i}\sum_{i<n}(uv^{-1})^{i}((uv^{-1})^{m})^{-1}((uv^{-1})^{n})^{-1}\bigr)\Bigr]$$
--   equals
--   $$\sum_{x\in\mathrm{Sols}\,M}\ \sum_{i<m}\ \sum_{i'<n} m\,n\Bigl[F_u(i+i'+1)F_v(m+n-1-i-i')-F_u(i+i'+1-n)F_v(i+i'+1-m)+2\bigl(F_u(i+i'+1)-F_u(i+i'+1-n)\bigr)+2\bigl(F_v(m+n-1-i-i')-F_v(i+i'+1-m)\bigr)\Bigr],$$
--   the arguments of $F_u,F_v$ on the right being integers (the indices $i,i'$ cast to $\mathbb{Z}$).
--
--   (12) For $K$ of characteristic zero, under `hu0`, `hu1`, `hv0`, `hv1`, for all $M$,
--   $$\sum_{d\mid M} d\Bigl(\sum_{j=1}^{d} T_v(j)\,T_u(d+1-j)-\sum_{j<d} T_v(j)\,T_u(d-1-j)\Bigr)$$
--   equals $\sum_{d\mid M} d$ times the difference of two inner sums: over $j\in[1,d]$ of
--   $$j^{2}(d+1-j)^{2}+j^{2}\!\!\sum_{l=1}^{d-j}\!(d+1-j-l)F_u(l)+(d+1-j)^{2}\!\sum_{l=1}^{j-1}\!(j-l)F_v(l)+\sum_{l=1}^{j-1}\sum_{l'=1}^{d-j}(j-l)(d+1-j-l')F_v(l)F_u(l'),$$
--   minus the sum over $j<d$ of the same expression with $d+1-j$ replaced throughout by $d-1-j$.
--
--   (13) For $K$ of characteristic zero, under `hu0`, `hu1`, `hv0`, `hv1`, for all $M$,
--   $$\sum_{d\mid M} d\Bigl(\bigl(F_v(d)+2\bigr)\sum_{k=1}^{d-1}(d-k)T_u(k)+\bigl(F_u(d)+2\bigr)\sum_{k=1}^{d-1}(d-k)T_v(k)-2\,T_u(d)T_v(d)\Bigr)$$
--   equals
--   $$\sum_{d\mid M} d\Bigl(\bigl(F_v(d)+2\bigr)\sum_{k=1}^{d-1}(d-k)\bigl(k^{2}+\sum_{l=1}^{k-1}(k-l)F_u(l)\bigr)+\bigl(F_u(d)+2\bigr)\sum_{k=1}^{d-1}(d-k)\bigl(k^{2}+\sum_{l=1}^{k-1}(k-l)F_v(l)\bigr)-2\bigl(d^{2}d^{2}+d^{2}\sum_{l=1}^{d-1}(d-l)F_u(l)+d^{2}\sum_{l=1}^{d-1}(d-l)F_v(l)+\sum_{l=1}^{d-1}\sum_{l'=1}^{d-1}(d-l)(d-l')F_v(l)F_u(l')\bigr)\Bigr).$$
--
--   (14) For $K$ of characteristic zero, under `hu0`, `hu1`, `hv0`, for all $M$,
--   $$\sum_{a=1}^{M-1}\bigl((\mathrm{xCoeff}\,(u*v)\,a)+(\mathrm{xCoeff}\,(u*v^{-1})\,a)\bigr)\Bigl(\sum_{e\mid M-a} e\,T_u(e)\Bigr)$$
--   equals
--   $$\sum_{a=1}^{M-1}\sum_{d\mid a}\sum_{e\mid M-a} d\,e\Bigl(F_v(d)\,S_u+2\,S_u+2F_v(d)\bigl(e^{2}+\sum_{l=1}^{e-1}(e-l)F_u(l)\bigr)\Bigr),\qquad S_u:=e^{2}F_u(d)+\sum_{l=1}^{e-1}(e-l)\,\Delta_u(d,l).$$
--
--   (15) For $K$ of characteristic zero, under `hu0`, `hv0`, `hv1`, for all $M$, the same identity with the roles of $u$ and $v$ exchanged in the right-hand side and with $T_v$ on the left:
--   $$\sum_{a=1}^{M-1}\bigl((\mathrm{xCoeff}\,(u*v)\,a)+(\mathrm{xCoeff}\,(u*v^{-1})\,a)\bigr)\Bigl(\sum_{e\mid M-a} e\,T_v(e)\Bigr)=\sum_{a=1}^{M-1}\sum_{d\mid a}\sum_{e\mid M-a} d\,e\Bigl(F_u(d)\,S_v+2\,S_v+2F_u(d)\bigl(e^{2}+\sum_{l=1}^{e-1}(e-l)F_v(l)\bigr)\Bigr),$$
--   where $S_v:=e^{2}F_v(d)+\sum_{l=1}^{e-1}(e-l)\Delta_v(d,l)$.
--
--   (16) Under `hv0`, for all $u$ and $M$,
--   $$\sum_{a=1}^{M-1}\Bigl(\sum_{d\mid a} d\,\bigl(F_v(d)+2\bigr)T_u(d)\Bigr)(\mathrm{xCoeff}\ v\ (M-a))=\sum_{a=1}^{M-1}\sum_{d\mid a}\sum_{d'\mid M-a} d\,d'\,\bigl(F_v(d+d')+F_v(d-d')-2F_v(d)\bigr)T_u(d),$$
--   the inner bracket carrying only the correction $-2F_v(d)$ (not the full second difference $\Delta_v(d,d')$).
--
--   (17) For $K$ of characteristic zero, under `hu0`, `hv0`, `hu1`, `hv1`, `huvm`, `huvd` and `hM : 0 < M`, the defect coefficient `addDefectSumCoeff u v M` — by definition the combination, at $M$, of full antidiagonal Cauchy products
--   $$\mathrm{cm}\bigl(X_{uv},\mathrm{cm}(X_u,X_u)\bigr)-2\,\mathrm{cm}\bigl(X_{uv},\mathrm{cm}(X_u,X_v)\bigr)+\mathrm{cm}\bigl(X_{uv},\mathrm{cm}(X_v,X_v)\bigr)+\mathrm{cm}\bigl(X_{uv^{-1}},\mathrm{cm}(X_u,X_u)\bigr)-2\,\mathrm{cm}\bigl(X_{uv^{-1}},\mathrm{cm}(X_u,X_v)\bigr)+\mathrm{cm}\bigl(X_{uv^{-1}},\mathrm{cm}(X_v,X_v)\bigr)-2\,\mathrm{cm}\bigl(X_u,\mathrm{cm}(X_u,X_v)\bigr)-2\,\mathrm{cm}\bigl(X_u,\mathrm{cm}(X_v,X_v)\bigr)-\mathrm{cm}(X_u,X_v)-2\,\mathrm{cm}(\mathrm{a₄Coeff},X_u)-2\,\mathrm{cm}(\mathrm{a₄Coeff},X_v)-4\,\mathrm{a₆Coeff},$$
--   where $\mathrm{cm}=$ `cauchyMul` and $X_w=$ `xCoeffFull w` — is equal to the absorbed expression consisting of: the closed-form $\mathrm{Sols}$-sum appearing on the left of (11); minus twice the divisor sum appearing on the left of (12); plus the divisor sum appearing on the left of (13); plus
--   $$\sum_{a=1}^{M-1}\Bigl[\bigl(\mathrm{xCoeff}\,(u*v)\,a+\mathrm{xCoeff}\,(u*v^{-1})\,a\bigr)\Bigl(2\bigl(\sum_{e\mid M-a} e\,T_u(e)+\sum_{e\mid M-a} e\,T_v(e)\bigr)+\mathrm{cauchyMulInt}\,(X_u-X_v)\,(X_u-X_v)\,(M-a)\Bigr)-2\Bigl(\sum_{d\mid a} d\bigl(F_v(d)+2\bigr)T_u(d)\Bigr)\mathrm{xCoeff}\ v\ (M-a)-2\Bigl(\sum_{d\mid a} d\bigl(F_u(d)+2\bigr)T_v(d)\Bigr)\mathrm{xCoeff}\ u\ (M-a)\Bigr]$$
--   (the middle convolution being the truncated convolution of the sequence $i\mapsto X_u(i)-X_v(i)$ with itself); minus $4\sum_{x\in\mathrm{Sols}M} m\,T_u(m)\,(\mathrm{xDivTerm}\ v\ n)$; minus $4\sum_{x\in\mathrm{Sols}M}(\mathrm{xDivTerm}\ u\ m)\bigl(n\,T_v(n)\bigr)$; minus twice `cauchyMulIntTriple (xCoeffFull u) (xCoeffFull u) (xCoeffFull v) M`; minus twice `cauchyMulIntTriple (xCoeffFull u) (xCoeffFull v) (xCoeffFull v) M`; minus `cauchyMulInt (xCoeffFull u) (xCoeffFull v) M`; minus $2\,$`cauchyMulInt a₄Coeff (xCoeffFull u) M`; minus $2\,$`cauchyMulInt a₄Coeff (xCoeffFull v) M`; minus $4\,$`a₆Coeff M`.
--
--   (18) Under `hu0`, `hv0` and `huvd`, for every $M$, the symmetry `addDefectSumCoeff v u M = addDefectSumCoeff u v M`.
--
--   These eighteen identities form the interface of the row-form and three-bin layer in the $q$-expansion verification that the Tate parametrisation of $y^{2}+xy=x^{3}+a_4(q)x+a_6(q)$ satisfies the symmetric addition identities: the coefficients of the addition defect are rewritten, bin by bin, as sums of products $F_u(\cdot)F_v(\cdot)$ of the normalised Weierstrass kernels, the constant bin is shown to vanish, and the resulting absorbed form is recorded together with its symmetry in $u,v$. They are used by [`TateCurve.ks17_C3_exports`](thm.html#TateCurve.ks17_C3_exports), [`TateCurve.ks17_D3_exports`](thm.html#TateCurve.ks17_D3_exports) and [`TateCurve.symAdd_sum_regional`](thm.html#TateCurve.symAdd_sum_regional).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TateCurve_ks17_C2_exports.lean

import Mathlib
import Definitions.Def_TateCurve_XMultIdentities
import Definitions.Def_TateCurve_KeystoneVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped NNReal
open TateCurve FLT.DivisorConvolution FLT.DivisorConvolution.BesgeCertificate Finset

theorem TateCurve.ks17_C2_exports.{u_1} :

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] (u v : K) (M : ℕ),
      cauchyMulInt (xCoeffFull u) (xCoeffFull v) M = ∑ x ∈ Sols M, (x.1 : K) * (x.2.2.1 : K) * Fz u (x.1 : ℤ) * Fz v (x.2.2.1 : ℤ)) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] (u : K) (M : ℕ),
      cauchyMulInt a₄Coeff (xCoeffFull u) M = -(∑ x ∈ Sols M, ((5 * x.1 ^ 3 : ℕ) : K) * ((x.2.2.1 : K) * Fz u (x.2.2.1 : ℤ)))) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u : K} [CharZero K] (hu0 : u ≠ 0) (hu1 : u ≠ 1) (v : K)
    (M : ℕ),
      ∑ x ∈ Sols M, (x.1 : K) * tent u x.1 * xDivTerm v x.2.2.1 = (∑ x ∈ Sols M, (x.1 : K) ^ 3 * (x.2.2.1 : K) * Fz v (x.2.2.1 : ℤ)) + ∑ x ∈ Sols M, ∑ j ∈ Finset.Ico 1 x.1, (x.1 : K) * ((x.1 - j : ℕ) : K) * (x.2.2.1 : K) * Fz u (j : ℤ) * Fz v (x.2.2.1 : ℤ)) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {v : K} [CharZero K] (u : K) (hv0 : v ≠ 0) (hv1 : v ≠ 1)
    (M : ℕ),
      ∑ x ∈ Sols M, xDivTerm u x.1 * ((x.2.2.1 : K) * tent v x.2.2.1) = (∑ x ∈ Sols M, (x.2.2.1 : K) ^ 3 * (x.1 : K) * Fz u (x.1 : ℤ)) + ∑ x ∈ Sols M, ∑ j ∈ Finset.Ico 1 x.2.2.1, (x.2.2.1 : K) * ((x.2.2.1 - j : ℕ) : K) * (x.1 : K) * Fz u (x.1 : ℤ) * Fz v (j : ℤ)) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u : K} (hu0 : u ≠ 0) (v : K) (M : ℕ),
      cauchyMulIntTriple (xCoeffFull u) (xCoeffFull u) (xCoeffFull v) M = ∑ i ∈ Finset.Ico 1 M, ∑ d ∈ i.divisors, ∑ x ∈ Sols (M - i), (d : K) * (x.1 : K) * (x.2.2.1 : K) * (Fz u ((d : ℤ) + (x.1 : ℤ)) + Fz u ((d : ℤ) - (x.1 : ℤ)) - 2 * Fz u (d : ℤ) - 2 * Fz u (x.1 : ℤ)) * Fz v (x.2.2.1 : ℤ)) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {v : K} (u : K) (hv0 : v ≠ 0) (M : ℕ),
      cauchyMulIntTriple (xCoeffFull u) (xCoeffFull v) (xCoeffFull v) M = ∑ i ∈ Finset.Ico 1 M, ∑ d ∈ i.divisors, ∑ x ∈ Sols (M - i), (d : K) * (x.1 : K) * (x.2.2.1 : K) * Fz u (d : ℤ) * (Fz v ((x.1 : ℤ) + (x.2.2.1 : ℤ)) + Fz v ((x.1 : ℤ) - (x.2.2.1 : ℤ)) - 2 * Fz v (x.1 : ℤ) - 2 * Fz v (x.2.2.1 : ℤ))) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} (hu0 : u ≠ 0) (d a : ℤ),
      (Fz u d * Fz v d + 2 * Fz u d + 2 * Fz v d) * Fz u a = Fz v d * (Fz u (d + a) + Fz u (d - a) - 2 * Fz u d - 2 * Fz u a) + 2 * (Fz u (d + a) + Fz u (d - a) - 2 * Fz u d - 2 * Fz u a) + 2 * Fz v d * Fz u a) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} (hv0 : v ≠ 0) (d a : ℤ),
      (Fz u d * Fz v d + 2 * Fz u d + 2 * Fz v d) * Fz v a = Fz u d * (Fz v (d + a) + Fz v (d - a) - 2 * Fz v d - 2 * Fz v a) + 2 * (Fz v (d + a) + Fz v (d - a) - 2 * Fz v d - 2 * Fz v a) + 2 * Fz u d * Fz v a) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} (hu0 : u ≠ 0) (hv0 : v ≠ 0) (a b c d : ℤ),
      (Fz u a * Fz v b) * (Fz u c * Fz v d) = (Fz u (a + c) + Fz u (a - c) - 2 * Fz u a - 2 * Fz u c) * (Fz v (b + d) + Fz v (b - d) - 2 * Fz v b - 2 * Fz v d)) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [CharZero K] {M : ℕ} (hM : 0 < M),
      -2 * ∑ d ∈ M.divisors, (d : K) * ((∑ j ∈ Finset.Icc 1 d, (j : K) ^ 2 * ((d + 1 - j : ℕ) : K) ^ 2) - ∑ j ∈ Finset.range d, (j : K) ^ 2 * ((d - 1 - j : ℕ) : K) ^ 2) + ∑ d ∈ M.divisors, (d : K) * (2 * ∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) * (k : K) ^ 2 + 2 * ∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) * (k : K) ^ 2 - 2 * ((d : K) ^ 2 * (d : K) ^ 2)) - 4 * a₆Coeff M = 0) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} (hu0 : u ≠ 0) (hv0 : v ≠ 0) (M : ℕ),
      (∑ x ∈ Sols M, (x.1 : K) * (x.2.2.1 : K) * ((u ^ x.1 - v ^ x.1) * (u ^ x.2.2.1 - v ^ x.2.2.1) * (u * v * (∑ i ∈ Finset.range x.1, (u * v) ^ i) * (∑ i ∈ Finset.range x.2.2.1, (u * v) ^ i) * ((u * v) ^ x.1)⁻¹ * ((u * v) ^ x.2.2.1)⁻¹) + (u ^ x.1 - (v ^ x.1)⁻¹) * (u ^ x.2.2.1 - (v ^ x.2.2.1)⁻¹) * (u * v⁻¹ * (∑ i ∈ Finset.range x.1, (u * v⁻¹) ^ i) * (∑ i ∈ Finset.range x.2.2.1, (u * v⁻¹) ^ i) * ((u * v⁻¹) ^ x.1)⁻¹ * ((u * v⁻¹) ^ x.2.2.1)⁻¹))) = ∑ x ∈ Sols M, ∑ i ∈ Finset.range x.1, ∑ i' ∈ Finset.range x.2.2.1, (x.1 : K) * (x.2.2.1 : K) * (Fz u ((i : ℤ) + i' + 1) * Fz v ((x.1 : ℤ) + x.2.2.1 - 1 - i - i') - Fz u ((i : ℤ) + i' + 1 - x.2.2.1) * Fz v ((i : ℤ) + i' + 1 - x.1) + 2 * (Fz u ((i : ℤ) + i' + 1) - Fz u ((i : ℤ) + i' + 1 - x.2.2.1)) + 2 * (Fz v ((x.1 : ℤ) + x.2.2.1 - 1 - i - i') - Fz v ((i : ℤ) + i' + 1 - x.1)))) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} [CharZero K] (hu0 : u ≠ 0) (hu1 : u ≠ 1) (hv0 : v ≠ 0) (hv1 : v ≠ 1)
    (M : ℕ),
      ∑ d ∈ M.divisors, (d : K) * ((∑ j ∈ Finset.Icc 1 d, tent v j * tent u (d + 1 - j)) - ∑ j ∈ Finset.range d, tent v j * tent u (d - 1 - j)) = ∑ d ∈ M.divisors, (d : K) * ((∑ j ∈ Finset.Icc 1 d, ((j : K) ^ 2 * ((d + 1 - j : ℕ) : K) ^ 2 + (j : K) ^ 2 * (∑ l ∈ Finset.Ico 1 (d + 1 - j), ((d + 1 - j - l : ℕ) : K) * Fz u (l : ℤ)) + ((d + 1 - j : ℕ) : K) ^ 2 * (∑ l ∈ Finset.Ico 1 j, ((j - l : ℕ) : K) * Fz v (l : ℤ)) + ∑ l ∈ Finset.Ico 1 j, ∑ l' ∈ Finset.Ico 1 (d + 1 - j), ((j - l : ℕ) : K) * ((d + 1 - j - l' : ℕ) : K) * Fz v (l : ℤ) * Fz u (l' : ℤ))) - ∑ j ∈ Finset.range d, ((j : K) ^ 2 * ((d - 1 - j : ℕ) : K) ^ 2 + (j : K) ^ 2 * (∑ l ∈ Finset.Ico 1 (d - 1 - j), ((d - 1 - j - l : ℕ) : K) * Fz u (l : ℤ)) + ((d - 1 - j : ℕ) : K) ^ 2 * (∑ l ∈ Finset.Ico 1 j, ((j - l : ℕ) : K) * Fz v (l : ℤ)) + ∑ l ∈ Finset.Ico 1 j, ∑ l' ∈ Finset.Ico 1 (d - 1 - j), ((j - l : ℕ) : K) * ((d - 1 - j - l' : ℕ) : K) * Fz v (l : ℤ) * Fz u (l' : ℤ)))) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} [CharZero K] (hu0 : u ≠ 0) (hu1 : u ≠ 1) (hv0 : v ≠ 0)
    (hv1 : v ≠ 1) (M : ℕ),
      ∑ d ∈ M.divisors, (d : K) * ((Fz v (d : ℤ) + 2) * (∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) * tent u k) + (Fz u (d : ℤ) + 2) * (∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) * tent v k) - 2 * (tent u d * tent v d)) = ∑ d ∈ M.divisors, (d : K) * ((Fz v (d : ℤ) + 2) * (∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) * ((k : K) ^ 2 + ∑ l ∈ Finset.Ico 1 k, ((k - l : ℕ) : K) * Fz u (l : ℤ))) + (Fz u (d : ℤ) + 2) * (∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) * ((k : K) ^ 2 + ∑ l ∈ Finset.Ico 1 k, ((k - l : ℕ) : K) * Fz v (l : ℤ))) - 2 * ((d : K) ^ 2 * (d : K) ^ 2 + (d : K) ^ 2 * (∑ l ∈ Finset.Ico 1 d, ((d - l : ℕ) : K) * Fz u (l : ℤ)) + (d : K) ^ 2 * (∑ l ∈ Finset.Ico 1 d, ((d - l : ℕ) : K) * Fz v (l : ℤ)) + ∑ l ∈ Finset.Ico 1 d, ∑ l' ∈ Finset.Ico 1 d, ((d - l : ℕ) : K) * ((d - l' : ℕ) : K) * Fz v (l : ℤ) * Fz u (l' : ℤ)))) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} [CharZero K] (hu0 : u ≠ 0) (hu1 : u ≠ 1) (hv0 : v ≠ 0)
    (M : ℕ),
      ∑ a ∈ Finset.Ico 1 M, (xCoeff (u * v) a + xCoeff (u * v⁻¹) a) * (∑ e ∈ (M - a).divisors, (e : K) * tent u e) = ∑ a ∈ Finset.Ico 1 M, ∑ d ∈ a.divisors, ∑ e ∈ (M - a).divisors, (d : K) * (e : K) * (Fz v (d : ℤ) * ((e : K) ^ 2 * Fz u (d : ℤ) + ∑ l ∈ Finset.Ico 1 e, ((e - l : ℕ) : K) * (Fz u ((d : ℤ) + (l : ℤ)) + Fz u ((d : ℤ) - (l : ℤ)) - 2 * Fz u (d : ℤ) - 2 * Fz u (l : ℤ))) + 2 * ((e : K) ^ 2 * Fz u (d : ℤ) + ∑ l ∈ Finset.Ico 1 e, ((e - l : ℕ) : K) * (Fz u ((d : ℤ) + (l : ℤ)) + Fz u ((d : ℤ) - (l : ℤ)) - 2 * Fz u (d : ℤ) - 2 * Fz u (l : ℤ))) + 2 * Fz v (d : ℤ) * ((e : K) ^ 2 + ∑ l ∈ Finset.Ico 1 e, ((e - l : ℕ) : K) * Fz u (l : ℤ)))) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} [CharZero K] (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hv1 : v ≠ 1)
    (M : ℕ),
      ∑ a ∈ Finset.Ico 1 M, (xCoeff (u * v) a + xCoeff (u * v⁻¹) a) * (∑ e ∈ (M - a).divisors, (e : K) * tent v e) = ∑ a ∈ Finset.Ico 1 M, ∑ d ∈ a.divisors, ∑ e ∈ (M - a).divisors, (d : K) * (e : K) * (Fz u (d : ℤ) * ((e : K) ^ 2 * Fz v (d : ℤ) + ∑ l ∈ Finset.Ico 1 e, ((e - l : ℕ) : K) * (Fz v ((d : ℤ) + (l : ℤ)) + Fz v ((d : ℤ) - (l : ℤ)) - 2 * Fz v (d : ℤ) - 2 * Fz v (l : ℤ))) + 2 * ((e : K) ^ 2 * Fz v (d : ℤ) + ∑ l ∈ Finset.Ico 1 e, ((e - l : ℕ) : K) * (Fz v ((d : ℤ) + (l : ℤ)) + Fz v ((d : ℤ) - (l : ℤ)) - 2 * Fz v (d : ℤ) - 2 * Fz v (l : ℤ))) + 2 * Fz u (d : ℤ) * ((e : K) ^ 2 + ∑ l ∈ Finset.Ico 1 e, ((e - l : ℕ) : K) * Fz v (l : ℤ)))) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} (hv0 : v ≠ 0) (M : ℕ),
      ∑ a ∈ Finset.Ico 1 M, (∑ d ∈ a.divisors, (d : K) * (Fz v (d : ℤ) + 2) * tent u d) * xCoeff v (M - a) = ∑ a ∈ Finset.Ico 1 M, ∑ d ∈ a.divisors, ∑ d' ∈ (M - a).divisors, (d : K) * (d' : K) * ((Fz v ((d : ℤ) + (d' : ℤ)) + Fz v ((d : ℤ) - (d' : ℤ)) - 2 * Fz v (d : ℤ)) * tent u d)) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} [CharZero K] (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hu1 : u ≠ 1)
    (hv1 : v ≠ 1) (huvm : u * v ≠ 1) (huvd : u * v⁻¹ ≠ 1) {M : ℕ} (hM : 0 < M),
      addDefectSumCoeff u v M = (∑ x ∈ Sols M, (x.1 : K) * (x.2.2.1 : K) * ((u ^ x.1 - v ^ x.1) * (u ^ x.2.2.1 - v ^ x.2.2.1) * (u * v * (∑ i ∈ Finset.range x.1, (u * v) ^ i) * (∑ i ∈ Finset.range x.2.2.1, (u * v) ^ i) * ((u * v) ^ x.1)⁻¹ * ((u * v) ^ x.2.2.1)⁻¹) + (u ^ x.1 - (v ^ x.1)⁻¹) * (u ^ x.2.2.1 - (v ^ x.2.2.1)⁻¹) * (u * v⁻¹ * (∑ i ∈ Finset.range x.1, (u * v⁻¹) ^ i) * (∑ i ∈ Finset.range x.2.2.1, (u * v⁻¹) ^ i) * ((u * v⁻¹) ^ x.1)⁻¹ * ((u * v⁻¹) ^ x.2.2.1)⁻¹))) - 2 * ∑ d ∈ M.divisors, (d : K) * ((∑ j ∈ Finset.Icc 1 d, tent v j * tent u (d + 1 - j)) - ∑ j ∈ Finset.range d, tent v j * tent u (d - 1 - j)) + (∑ d ∈ M.divisors, (d : K) * ((Fz v (d : ℤ) + 2) * (∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) * tent u k) + (Fz u (d : ℤ) + 2) * (∑ k ∈ Finset.Ico 1 d, ((d - k : ℕ) : K) * tent v k) - 2 * (tent u d * tent v d))) + (∑ a ∈ Finset.Ico 1 M, ((xCoeff (u * v) a + xCoeff (u * v⁻¹) a) * (2 * ((∑ e ∈ (M - a).divisors, (e : K) * tent u e) + ∑ e ∈ (M - a).divisors, (e : K) * tent v e) + cauchyMulInt (fun i => xCoeffFull u i - xCoeffFull v i) (fun i => xCoeffFull u i - xCoeffFull v i) (M - a)) - 2 * ((∑ d ∈ a.divisors, (d : K) * (Fz v (d : ℤ) + 2) * tent u d) * xCoeff v (M - a)) - 2 * ((∑ d ∈ a.divisors, (d : K) * (Fz u (d : ℤ) + 2) * tent v d) * xCoeff u (M - a)))) - 4 * ∑ x ∈ Sols M, (x.1 : K) * tent u x.1 * xDivTerm v x.2.2.1 - 4 * ∑ x ∈ Sols M, xDivTerm u x.1 * ((x.2.2.1 : K) * tent v x.2.2.1) - 2 * cauchyMulIntTriple (xCoeffFull u) (xCoeffFull u) (xCoeffFull v) M - 2 * cauchyMulIntTriple (xCoeffFull u) (xCoeffFull v) (xCoeffFull v) M - cauchyMulInt (xCoeffFull u) (xCoeffFull v) M - 2 * cauchyMulInt a₄Coeff (xCoeffFull u) M - 2 * cauchyMulInt a₄Coeff (xCoeffFull v) M - 4 * a₆Coeff M) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] {u v : K} [IsUltrametricDist K] [CompleteSpace K] (hu0 : u ≠ 0) (hv0 : v ≠ 0) (huvd : u * v⁻¹ ≠ 1) (M : ℕ),
      addDefectSumCoeff v u M = addDefectSumCoeff u v M) := by sorry
