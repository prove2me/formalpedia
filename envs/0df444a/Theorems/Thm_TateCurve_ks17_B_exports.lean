-- Prove2me | Theorems.Thm_TateCurve_ks17_B_exports
-- name    : TateCurve.ks17_B_exports
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/78bc46b5-2d3c-5aa4-a722-9c594b02780e
-- title:
--   Export bundle B: divisor convolutions and Tate-curve defect normal forms
-- statement:
--   A single conjunction of twenty-one identities belonging to the $q$-expansion layer of the Tate parametrisation; each conjunct quantifies over its own ambient field and parameters.
--
--   Notation and unfoldings used below. For a field $K$ (in each conjunct nontrivially normed, in most conjuncts also with ultrametric distance and complete) and $u\in K$, $a\in\mathbb Z$, put $F_u(a)=u^{a}+u^{-a}-2$ (`Fz`) and $G_u(a)=u^{a}-u^{-a}$ (`Gz`), integer powers being `zpow`; for $m\in\mathbb N$ put $T_u(m)=u\bigl(\sum_{i<m}u^{i}\bigr)^{2}(u^{m})^{-1}$ (`tent`); and $x(w)=w/(1-w)^{2}$ (`xfun`). Write $x_N(u)=$ `xCoeff u N` $=\sum_{d\mid N}$ `xDivTerm u d`, and let `xCoeffFull u` be the sequence taking the value $x(u)$ at $0$ and $x_N(u)$ at $N\ge 1$, `yCoeffFull u` the sequence taking the value `yfun u` at $0$ and `yCoeff u N` at $N\ge1$, and `psiCoeffFull u N` $=2\,$`yCoeffFull u N`$+$`xCoeffFull u N`. The convolutions are `cauchyMul c d N` $=\sum_{k+l=N}c(k)d(l)$ over the antidiagonal, `cauchyMulInt c d N` $=\sum_{i=1}^{N-1}c(i)d(N-i)$, and `cauchyMulIntTriple c d e N` $=\sum_{i=1}^{N-1}c(i)\,$`cauchyMulInt d e (N-i)`. Further, $\sigma_k(n)=\sum_{d\mid n}d^{k}$ (`sigma`), $\mathrm{Sols}(N)$ is the finite set of quadruples $(a,b,c,d)\in[1,N]^{4}$ of naturals with $ab+cd=N$, and `swap₁` is the map on quadruples of naturals used in the convolution certificate. The sequences `a₄Coeff` and `a₆Coeff` are the coefficient sequences of that name from the definition modules. All subtractions of naturals are truncated and all divisions of naturals are integer divisions; casts $\mathbb N\to\mathbb Z$ and $\mathbb N\to K$ are as in the Lean text. The combinations `addDefectSumCoeff`, `addDefectDiffCoeff` and `svComplex` are the explicit polynomial combinations of `cauchyMul`, `cauchyMulInt`, `xCoeffFull`, `psiCoeffFull`, `a₄Coeff`, `a₆Coeff`, `xfun`, `psifun`, `Gz` and `xCoeff` given by their definitions.
--
--   The conjuncts are the following.
--
--   (1) For $K$ nontrivially normed, ultrametric and complete, $w\in K$ with $w\neq 0$, and $e\in\mathbb N$: $G_w(1)\,T_w(e)=2\sum_{j=1}^{e-1}G_w(j)+G_w(e)$.
--
--   (2) For an additive commutative monoid $\beta$, $N\in\mathbb N$ and $F:\mathbb N^{4}\to\beta$: $\sum_{x\in\mathrm{Sols}(N)}F(x)=\sum_{x\in\mathrm{Sols}(N)}F(\mathtt{swap₁}\,x)$.
--
--   (3) For a commutative ring $A$, a function $f:\mathbb Z\to A$ with $f(0)=0$ and $f(-a)=f(a)$ for all $a$, and $M\in\mathbb N$:
--   $$6\sum_{(a,b,c,d)\in\mathrm{Sols}(M)}ac\bigl(f(a+c)+f(a-c)-2f(a)-2f(c)\bigr)=\sum_{\delta\mid M}(\delta^{3}-\delta)f(\delta)-12\sum_{\delta\mid M}\sum_{k=1}^{\delta-1}\delta(\delta-k)f(k),$$
--   the summation variables $a$ and $c$ being the first and third coordinates of the quadruple.
--
--   (4) For $K$ ultrametric and complete, $u\neq 0$, $u\neq 1$ and $e\in\mathbb N$: $x(u)G_u(e)=e\,\bigl(x(u)G_u(1)\bigr)+G_u(1)\sum_{j<e/2}T_u(e-1-2j)$.
--
--   (5) For $K$ ultrametric and complete, $u,v\in K$ and $n\in\mathbb N$: $x_n(u)-x_n(v)=\sum_{f\mid n}f\bigl(F_u(f)-F_v(f)\bigr)$.
--
--   (6) For $K$ ultrametric, complete and of characteristic zero, $u,v\in K$ with $u\neq0$, $v\neq0$, $u\neq1$, $v\neq1$, $uv\neq1$, $uv^{-1}\neq1$, and $e\in\mathbb N$:
--   $$\bigl(x(uv)-x(uv^{-1})\bigr)\bigl((x(u)-x(v))(F_u(e)-F_v(e))\bigr)=e^{2}\bigl(x(u)G_u(1)\bigr)\bigl(x(v)G_v(1)\bigr)$$
--   $$+\,x(u)G_u(1)\sum_{m=1}^{e-1}(e-m)\bigl(G_v(1)T_v(m)\bigr)+x(v)G_v(1)\sum_{m=1}^{e-1}(e-m)\bigl(G_u(1)T_u(m)\bigr)$$
--   $$+\sum_{i<e}\Bigl[\Bigl(G_u(1)\!\!\sum_{j<(i+1)/2}\!\!T_u(i-2j)\Bigr)\Bigl(G_v(1)\!\!\sum_{j<(e-i)/2}\!\!T_v(e-i-1-2j)\Bigr)-\Bigl(G_u(1)\!\!\sum_{j<(e-1-i)/2}\!\!T_u(e-1-i-1-2j)\Bigr)\Bigl(G_v(1)\!\!\sum_{j<i/2}\!\!T_v(i-1-2j)\Bigr)\Bigr].$$
--
--   (7) For $K$ ultrametric and complete, $u,v\in K$ with $u\neq0$, $u\neq1$, $v\neq0$, $v\neq1$, and $M>0$:
--   $$\mathtt{svComplex}\,u\,v\,M=2\bigl(x(uv)-x(uv^{-1})\bigr)\bigl((x(u)-x(v))(x_M(u)-x_M(v))\bigr)-2x(u)x(v)\sum_{d\mid M}d\,G_u(d)G_v(d)$$
--   $$+\sum_{d\mid M}d\Bigl(G_v(d)\bigl(x(u)G_u(1)\textstyle\sum_{j<d/2}T_u(d-1-2j)\bigr)+G_u(d)\bigl(x(v)G_v(1)\textstyle\sum_{j<d/2}T_v(d-1-2j)\bigr)\Bigr)$$
--   $$+\sum_{a=1}^{M-1}\Bigl(\sum_{d\mid a}d\,G_u(d)G_v(d)\Bigr)\Bigl(2\sum_{f\mid M-a}f\bigl(T_u(f)+T_v(f)\bigr)\Bigr)-\sum_{a=1}^{M-1}\Bigl(\sum_{d\mid a}d\,G_u(d)G_v(d)\Bigr)\Bigl(2\bigl(x(u)x_{M-a}(v)+x(v)x_{M-a}(u)\bigr)\Bigr).$$
--
--   (8) For $K$ nontrivially normed, $v\in K$ and $a\in\mathbb Z$: $F_{v^{-1}}(a)=F_v(a)$.
--
--   (9) For $K$ ultrametric and complete, $c,d:\mathbb N\to K$ and $N\in\mathbb N$: `cauchyMul c d N = cauchyMul d c N`.
--
--   (10) For $K$ nontrivially normed of characteristic zero, $v\neq0$ and $M\in\mathbb N$:
--   $$\sum_{e\mid M}e^{3}F_v(e)+12\,\sigma_3(M)=6\,\mathtt{cauchyMulInt}\,(\mathtt{xCoeffFull}\;v)\,(\mathtt{xCoeffFull}\;v)\,M+x_M(v)+12\sum_{d\mid M}d\,T_v(d).$$
--
--   (11) For $K$ nontrivially normed, $u,v\in K$ with $u\neq0$, $v\neq0$, $u\neq1$, $v\neq1$, $uv\neq1$, $uv^{-1}\neq1$, and $d\in\mathbb N$:
--   $$\bigl(x(uv)+x(uv^{-1})\bigr)\bigl((x(u)-x(v))(F_u(d)-F_v(d))\bigr)=-\Bigl[(u-v)(u^{d}-v^{d})\Bigl(\sum_{i<d}(uv)^{i}\Bigr)\bigl((uv)^{d}\bigr)^{-1}+(u-v^{-1})\bigl(u^{d}-(v^{d})^{-1}\bigr)\Bigl(\sum_{i<d}(uv^{-1})^{i}\Bigr)\bigl((uv^{-1})^{d}\bigr)^{-1}\Bigr]\,x(u)x(v).$$
--
--   (12) For $K$ nontrivially normed, $u,v\in K$ and $M\in\mathbb N$: $x_M(u)-x_M(v)=\sum_{d\mid M}d\bigl(F_u(d)-F_v(d)\bigr)$; this is the identity of (5) with the ultrametric and completeness assumptions dropped.
--
--   (13) For $K$ nontrivially normed and $u,v\in K$ both nonzero, and $n\in\mathbb N$: $x_n(uv)+x_n(uv^{-1})=\sum_{d\mid n}d\bigl(F_u(d)F_v(d)+2F_u(d)+2F_v(d)\bigr)$.
--
--   (14) For $K$ nontrivially normed, $v\in K$ and $N\in\mathbb N$: $x_N(v)=\sum_{d\mid N}d\,F_v(d)$.
--
--   (15) For $K$ nontrivially normed, $u,v\in K$ nonzero with $uv\neq1$, and $a,b\in\mathbb N$:
--   $$x(uv)\bigl(F_u(a)-F_v(a)\bigr)\bigl(F_u(b)-F_v(b)\bigr)=(u^{a}-v^{a})(u^{b}-v^{b})\Bigl(uv\Bigl(\sum_{i<a}(uv)^{i}\Bigr)\Bigl(\sum_{i<b}(uv)^{i}\Bigr)\bigl((uv)^{a}\bigr)^{-1}\bigl((uv)^{b}\bigr)^{-1}\Bigr).$$
--
--   (16) For $K$ nontrivially normed, $u,v\in K$ nonzero with $uv^{-1}\neq1$, and $a,b\in\mathbb N$:
--   $$x(uv^{-1})\bigl(F_u(a)-F_v(a)\bigr)\bigl(F_u(b)-F_v(b)\bigr)=\bigl(u^{a}-(v^{a})^{-1}\bigr)\bigl(u^{b}-(v^{b})^{-1}\bigr)\Bigl(uv^{-1}\Bigl(\sum_{i<a}(uv^{-1})^{i}\Bigr)\Bigl(\sum_{i<b}(uv^{-1})^{i}\Bigr)\bigl((uv^{-1})^{a}\bigr)^{-1}\bigl((uv^{-1})^{b}\bigr)^{-1}\Bigr).$$
--
--   (17) For $K$ ultrametric and complete, $u,v\in K$ and $M>0$, writing $\Delta(i)=$ `xCoeffFull u i` $-$ `xCoeffFull v i`, the quantity `addDefectSumCoeff u v M` equals
--   $$\bigl(x(uv)+x(uv^{-1})\bigr)\mathtt{cauchyMulInt}\,\Delta\,\Delta\,M+2\bigl(x(uv)+x(uv^{-1})\bigr)\bigl((x(u)-x(v))(x_M(u)-x_M(v))\bigr)+\bigl(x_M(uv)+x_M(uv^{-1})\bigr)(x(u)-x(v))^{2}$$
--   $$+\sum_{a=1}^{M-1}\bigl(x_a(uv)+x_a(uv^{-1})\bigr)\Bigl(2(x(u)-x(v))\bigl(x_{M-a}(u)-x_{M-a}(v)\bigr)+\mathtt{cauchyMulInt}\,\Delta\,\Delta\,(M-a)\Bigr)$$
--   $$-\Bigl(2x(u)^{2}x_M(v)+4x(u)x(v)x_M(u)+4x(u)\,C(u,v)+2x(v)\,C(u,u)+2\,\mathtt{cauchyMulIntTriple}\,(\mathtt{xCoeffFull}\,u)(\mathtt{xCoeffFull}\,u)(\mathtt{xCoeffFull}\,v)\,M\Bigr)$$
--   $$-\Bigl(4x(u)x(v)x_M(v)+2x(u)\,C(v,v)+2x(v)^{2}x_M(u)+4x(v)\,C(u,v)+2\,\mathtt{cauchyMulIntTriple}\,(\mathtt{xCoeffFull}\,u)(\mathtt{xCoeffFull}\,v)(\mathtt{xCoeffFull}\,v)\,M\Bigr)$$
--   $$-\bigl(x(u)x_M(v)+x(v)x_M(u)+C(u,v)\bigr)-\bigl(2\,\mathtt{a₄Coeff}\,M\cdot x(u)+2\,\mathtt{cauchyMulInt}\,\mathtt{a₄Coeff}\,(\mathtt{xCoeffFull}\,u)\,M\bigr)$$
--   $$-\bigl(2\,\mathtt{a₄Coeff}\,M\cdot x(v)+2\,\mathtt{cauchyMulInt}\,\mathtt{a₄Coeff}\,(\mathtt{xCoeffFull}\,v)\,M\bigr)-4\,\mathtt{a₆Coeff}\,M,$$
--   where $C(s,t)$ abbreviates $\mathtt{cauchyMulInt}\,(\mathtt{xCoeffFull}\,s)(\mathtt{xCoeffFull}\,t)\,M$.
--
--   (18) For $K$ ultrametric and complete, $u,v\in K$ and $M\in\mathbb N$:
--   $$\mathtt{cauchyMulInt}\,(\mathtt{psiCoeffFull}\,u)(\mathtt{psiCoeffFull}\,v)\,M=\sum_{i=1}^{M-1}\ \sum_{d\mid i}\ \sum_{e\mid M-i}d^{2}e^{2}\,G_u(d)G_v(e).$$
--
--   (19) For $K$ ultrametric and complete, $u\neq0$ and $a,b,c\in\mathbb Z$:
--   $$F_u(a)F_u(b)G_u(c)=G_u(a+b+c)-G_u(a+b-c)+G_u(a-b+c)-G_u(a-b-c)-2G_u(a+c)+2G_u(a-c)-2G_u(b+c)+2G_u(b-c)+4G_u(c).$$
--
--   (20) For $K$ ultrametric and complete, $u,v\in K$ with $u\neq0$, $v\neq0$, $uv\neq1$, $uv^{-1}\neq1$, and $M>0$, with $\Delta$ as in (17), the quantity `addDefectDiffCoeff u v M` equals
--   $$\sum_{b=1}^{M-1}\sum_{d\mid b}\sum_{e\mid M-b}de\sum_{i<d}\sum_{i'<e}\Bigl(G_u(i+i'+1)G_v(i+i'+1-d-e)-G_u(i+i'+1-e)G_v(i+i'+1-d)\Bigr)$$
--   $$+\sum_{b=1}^{M-1}\Bigl(\sum_{d\mid b}d\,G_u(d)G_v(d)\Bigr)\mathtt{cauchyMulInt}\,\Delta\,\Delta\,(M-b)+\mathtt{cauchyMulInt}\,(\mathtt{psiCoeffFull}\,u)(\mathtt{psiCoeffFull}\,v)\,M+\mathtt{svComplex}\,u\,v\,M.$$
--
--   (21) For $K$ ultrametric and complete, $u,v\in K$ both nonzero, and $M\in\mathbb N$, with $\Delta$ as in (17):
--   $$\sum_{b=1}^{M-1}\Bigl(\sum_{d\mid b}d\,G_u(d)G_v(d)\Bigr)\mathtt{cauchyMulInt}\,\Delta\,\Delta\,(M-b)=\sum_{b=1}^{M-1}\sum_{d\mid b}\ \sum_{c=1}^{M-b-1}\ \sum_{e\mid c}\ \sum_{f\mid M-b-c}def\;\Bigl[\,\Phi_u(e,f,d)\,G_v(d)$$
--   $$-\bigl(G_u(e+d)-G_u(e-d)-2G_u(d)\bigr)\bigl(G_v(f+d)-G_v(f-d)-2G_v(d)\bigr)-\bigl(G_u(f+d)-G_u(f-d)-2G_u(d)\bigr)\bigl(G_v(e+d)-G_v(e-d)-2G_v(d)\bigr)+G_u(d)\,\Phi_v(e,f,d)\Bigr],$$
--   where $\Phi_w(e,f,d)=G_w(e+f+d)-G_w(e+f-d)+G_w(e-f+d)-G_w(e-f-d)-2G_w(e+d)+2G_w(e-d)-2G_w(f+d)+2G_w(f-d)+4G_w(d)$, that is, the right-hand side of (19) for the arguments $e,f,d$.
--
--   This is the bundled interface of the divisor-convolution and defect-normal-form layer of the analytic treatment of the Tate parametrisation: a Besge–Liouville type convolution identity for even functions on $\mathbb Z$, the Laurent identities satisfied by the series $F_u$, $G_u$ and the tent functions, the $\varphi$-identity relating $\sum_{e\mid M}e^3F_v(e)$ to a Cauchy square of the $x$-coefficients, and normal forms for the sum- and difference-defect coefficients of the addition law. It is built on [`TateCurve.ks17_A_exports`](thm.html#TateCurve.ks17_A_exports) together with the $q$-expansions of the Tate coordinates, and is consumed by [`TateCurve.diffHyp_unconditional`](thm.html#TateCurve.diffHyp_unconditional), [`TateCurve.ks17_C1_exports`](thm.html#TateCurve.ks17_C1_exports) and [`TateCurve.ks17_C2_exports`](thm.html#TateCurve.ks17_C2_exports) on the way to the symmetric addition identities for the Tate curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TateCurve_ks17_B_exports.lean

import Mathlib
import Definitions.Def_TateCurve_XMultIdentities
import Definitions.Def_TateCurve_KeystoneVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped NNReal
open TateCurve FLT.DivisorConvolution FLT.DivisorConvolution.BesgeCertificate Finset

theorem TateCurve.ks17_B_exports.{u_1} :

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] (w : K) (hw0 : w ≠ 0) (e : ℕ),
      Gz w 1 * tent w e = 2 * ∑ j ∈ Finset.Ico 1 e, Gz w (j : ℤ) + Gz w (e : ℤ)) ∧

    (∀ {β : Type u_1} [AddCommMonoid β] (N : ℕ) (F : ℕ × ℕ × ℕ × ℕ → β),
      ∑ x ∈ Sols N, F x = ∑ x ∈ Sols N, F (swap₁ x)) ∧

    (∀ {A : Type u_1} [CommRing A] (f : ℤ → A) (hf0 : f 0 = 0) (hfneg : ∀ a : ℤ, f (-a) = f a) (M : ℕ),
      6 * ∑ x ∈ Sols M, (x.1 : A) * (x.2.2.1 : A) * (f ((x.1 : ℤ) + (x.2.2.1 : ℤ)) + f ((x.1 : ℤ) - (x.2.2.1 : ℤ)) - 2 * f (x.1 : ℤ) - 2 * f (x.2.2.1 : ℤ)) = ∑ δ ∈ M.divisors, ((δ : A) ^ 3 - (δ : A)) * f (δ : ℤ) - 12 * ∑ δ ∈ M.divisors, ∑ k ∈ Finset.Ico 1 δ, (δ : A) * ((δ : A) - (k : A)) * f (k : ℤ)) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u : K} (hu0 : u ≠ 0) (hu1 : u ≠ 1) (e : ℕ),
      xfun u * Gz u (e : ℤ) = (e : K) * (xfun u * Gz u 1) + Gz u 1 * ∑ j ∈ Finset.range (e / 2), tent u (e - 1 - 2 * j)) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] (u v : K) (n : ℕ),
      xCoeff u n - xCoeff v n = ∑ f ∈ n.divisors, (f : K) * (Fz u (f : ℤ) - Fz v (f : ℤ))) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} [CharZero K] (hu0 : u ≠ 0)
    (hv0 : v ≠ 0) (hu1 : u ≠ 1) (hv1 : v ≠ 1) (huvm : u * v ≠ 1) (huvd : u * v⁻¹ ≠ 1) (e : ℕ),
      (xfun (u * v) - xfun (u * v⁻¹)) * ((xfun u - xfun v) * (Fz u (e : ℤ) - Fz v (e : ℤ))) = (e : K) ^ 2 * ((xfun u * Gz u 1) * (xfun v * Gz v 1)) + (xfun u * Gz u 1) * (∑ m ∈ Finset.Ico 1 e, ((e - m : ℕ) : K) * (Gz v 1 * tent v m)) + (xfun v * Gz v 1) * (∑ m ∈ Finset.Ico 1 e, ((e - m : ℕ) : K) * (Gz u 1 * tent u m)) + ∑ i ∈ Finset.range e, ((Gz u 1 * ∑ j ∈ Finset.range ((i + 1) / 2), tent u (i - 2 * j)) * (Gz v 1 * ∑ j ∈ Finset.range ((e - i) / 2), tent v (e - i - 1 - 2 * j)) - (Gz u 1 * ∑ j ∈ Finset.range ((e - 1 - i) / 2), tent u (e - 1 - i - 1 - 2 * j)) * (Gz v 1 * ∑ j ∈ Finset.range (i / 2), tent v (i - 1 - 2 * j)))) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} (hu0 : u ≠ 0) (hu1 : u ≠ 1) (hv0 : v ≠ 0) (hv1 : v ≠ 1)
    {M : ℕ} (hM : 0 < M),
      svComplex u v M = 2 * ((xfun (u * v) - xfun (u * v⁻¹)) * ((xfun u - xfun v) * (xCoeff u M - xCoeff v M))) - 2 * (xfun u * xfun v) * (∑ d ∈ M.divisors, (d : K) * (Gz u (d : ℤ) * Gz v (d : ℤ))) + (∑ d ∈ M.divisors, (d : K) * (Gz v (d : ℤ) * ((xfun u * Gz u 1) * ∑ j ∈ Finset.range (d / 2), tent u (d - 1 - 2 * j)) + Gz u (d : ℤ) * ((xfun v * Gz v 1) * ∑ j ∈ Finset.range (d / 2), tent v (d - 1 - 2 * j)))) + (∑ a ∈ Finset.Ico 1 M, (∑ d ∈ a.divisors, (d : K) * (Gz u (d : ℤ) * Gz v (d : ℤ))) * (2 * ∑ f ∈ (M - a).divisors, (f : K) * (tent u f + tent v f))) - ∑ a ∈ Finset.Ico 1 M, (∑ d ∈ a.divisors, (d : K) * (Gz u (d : ℤ) * Gz v (d : ℤ))) * (2 * (xfun u * xCoeff v (M - a) + xfun v * xCoeff u (M - a)))) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] {v : K} (a : ℤ),
      Fz v⁻¹ a = Fz v a) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] (c d : ℕ → K) (N : ℕ),
      cauchyMul c d N = cauchyMul d c N) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [CharZero K] {v : K} (hv : v ≠ 0) (M : ℕ),
      (∑ e ∈ M.divisors, (e : K) ^ 3 * Fz v (e : ℤ)) + 12 * (sigma 3 M : K) = 6 * cauchyMulInt (xCoeffFull v) (xCoeffFull v) M + xCoeff v M + 12 * ∑ d ∈ M.divisors, (d : K) * tent v d) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] {u v : K} (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hu1 : u ≠ 1)
    (hv1 : v ≠ 1) (huvm : u * v ≠ 1) (huvd : u * v⁻¹ ≠ 1) (d : ℕ),
      (xfun (u * v) + xfun (u * v⁻¹)) * ((xfun u - xfun v) * (Fz u (d : ℤ) - Fz v (d : ℤ))) = -(((u - v) * (u ^ d - v ^ d) * (∑ i ∈ Finset.range d, (u * v) ^ i) * ((u * v) ^ d)⁻¹ + (u - v⁻¹) * (u ^ d - (v ^ d)⁻¹) * (∑ i ∈ Finset.range d, (u * v⁻¹) ^ i) * ((u * v⁻¹) ^ d)⁻¹) * (xfun u * xfun v))) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] (u v : K) (M : ℕ),
      xCoeff u M - xCoeff v M = ∑ d ∈ M.divisors, (d : K) * (Fz u (d : ℤ) - Fz v (d : ℤ))) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] {u v : K} (hu : u ≠ 0) (hv : v ≠ 0) (n : ℕ),
      xCoeff (u * v) n + xCoeff (u * v⁻¹) n = ∑ d ∈ n.divisors, (d : K) * (Fz u (d : ℤ) * Fz v (d : ℤ) + 2 * Fz u (d : ℤ) + 2 * Fz v (d : ℤ))) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] (v : K) (N : ℕ),
      xCoeff v N = ∑ d ∈ N.divisors, (d : K) * Fz v (d : ℤ)) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] {u v : K} (hu : u ≠ 0) (hv : v ≠ 0) (huv1 : u * v ≠ 1)
    (a b : ℕ),
      xfun (u * v) * ((Fz u (a : ℤ) - Fz v (a : ℤ)) * (Fz u (b : ℤ) - Fz v (b : ℤ))) = (u ^ a - v ^ a) * (u ^ b - v ^ b) * (u * v * (∑ i ∈ Finset.range a, (u * v) ^ i) * (∑ i ∈ Finset.range b, (u * v) ^ i) * ((u * v) ^ a)⁻¹ * ((u * v) ^ b)⁻¹)) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] {u v : K} (hu : u ≠ 0) (hv : v ≠ 0) (huv1 : u * v⁻¹ ≠ 1)
    (a b : ℕ),
      xfun (u * v⁻¹) * ((Fz u (a : ℤ) - Fz v (a : ℤ)) * (Fz u (b : ℤ) - Fz v (b : ℤ))) = (u ^ a - (v ^ a)⁻¹) * (u ^ b - (v ^ b)⁻¹) * (u * v⁻¹ * (∑ i ∈ Finset.range a, (u * v⁻¹) ^ i) * (∑ i ∈ Finset.range b, (u * v⁻¹) ^ i) * ((u * v⁻¹) ^ a)⁻¹ * ((u * v⁻¹) ^ b)⁻¹)) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] (u v : K) {M : ℕ} (hM : 0 < M),
      addDefectSumCoeff u v M = ((xfun (u * v) + xfun (u * v⁻¹)) * cauchyMulInt (fun i => xCoeffFull u i - xCoeffFull v i) (fun i => xCoeffFull u i - xCoeffFull v i) M + 2 * ((xfun (u * v) + xfun (u * v⁻¹)) * ((xfun u - xfun v) * (xCoeff u M - xCoeff v M))) + (xCoeff (u * v) M + xCoeff (u * v⁻¹) M) * (xfun u - xfun v) ^ 2 + ∑ a ∈ Finset.Ico 1 M, (xCoeff (u * v) a + xCoeff (u * v⁻¹) a) * (2 * ((xfun u - xfun v) * (xCoeff u (M - a) - xCoeff v (M - a))) + cauchyMulInt (fun i => xCoeffFull u i - xCoeffFull v i) (fun i => xCoeffFull u i - xCoeffFull v i) (M - a))) - (2 * (xfun u ^ 2 * xCoeff v M) + 4 * (xfun u * xfun v * xCoeff u M) + 4 * (xfun u * cauchyMulInt (xCoeffFull u) (xCoeffFull v) M) + 2 * (xfun v * cauchyMulInt (xCoeffFull u) (xCoeffFull u) M) + 2 * cauchyMulIntTriple (xCoeffFull u) (xCoeffFull u) (xCoeffFull v) M) - (4 * (xfun u * xfun v * xCoeff v M) + 2 * (xfun u * cauchyMulInt (xCoeffFull v) (xCoeffFull v) M) + 2 * (xfun v ^ 2 * xCoeff u M) + 4 * (xfun v * cauchyMulInt (xCoeffFull u) (xCoeffFull v) M) + 2 * cauchyMulIntTriple (xCoeffFull u) (xCoeffFull v) (xCoeffFull v) M) - (xfun u * xCoeff v M + xfun v * xCoeff u M + cauchyMulInt (xCoeffFull u) (xCoeffFull v) M) - (2 * (a₄Coeff M * xfun u) + 2 * cauchyMulInt a₄Coeff (xCoeffFull u) M) - (2 * (a₄Coeff M * xfun v) + 2 * cauchyMulInt a₄Coeff (xCoeffFull v) M) - 4 * a₆Coeff M) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] (u v : K) (M : ℕ),
      cauchyMulInt (psiCoeffFull u) (psiCoeffFull v) M = ∑ i ∈ Finset.Ico 1 M, ∑ d ∈ i.divisors, ∑ e ∈ (M - i).divisors, (d : K) ^ 2 * (e : K) ^ 2 * (Gz u (d : ℤ) * Gz v (e : ℤ))) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u : K} (hu : u ≠ 0) (a b c : ℤ),
      Fz u a * Fz u b * Gz u c = Gz u (a + b + c) - Gz u (a + b - c) + Gz u (a - b + c) - Gz u (a - b - c) - 2 * Gz u (a + c) + 2 * Gz u (a - c) - 2 * Gz u (b + c) + 2 * Gz u (b - c) + 4 * Gz u c) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} (hu : u ≠ 0) (hv : v ≠ 0)
    (huvm : u * v ≠ 1) (huvd : u * v⁻¹ ≠ 1) {M : ℕ} (hM : 0 < M),
      addDefectDiffCoeff u v M = (∑ b ∈ Finset.Ico 1 M, ∑ d ∈ b.divisors, ∑ e ∈ (M - b).divisors, (d : K) * (e : K) * ∑ i ∈ Finset.range d, ∑ i' ∈ Finset.range e, (Gz u ((i : ℤ) + i' + 1) * Gz v ((i : ℤ) + i' + 1 - d - e) - Gz u ((i : ℤ) + i' + 1 - e) * Gz v ((i : ℤ) + i' + 1 - d))) + (∑ b ∈ Finset.Ico 1 M, (∑ d ∈ b.divisors, (d : K) * (Gz u (d : ℤ) * Gz v (d : ℤ))) * cauchyMulInt (fun i => xCoeffFull u i - xCoeffFull v i) (fun i => xCoeffFull u i - xCoeffFull v i) (M - b)) + cauchyMulInt (psiCoeffFull u) (psiCoeffFull v) M + svComplex u v M) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} (hu : u ≠ 0) (hv : v ≠ 0) (M : ℕ),
      ∑ b ∈ Finset.Ico 1 M, (∑ d ∈ b.divisors, (d : K) * (Gz u (d : ℤ) * Gz v (d : ℤ))) * cauchyMulInt (fun i => xCoeffFull u i - xCoeffFull v i) (fun i => xCoeffFull u i - xCoeffFull v i) (M - b) = ∑ b ∈ Finset.Ico 1 M, ∑ d ∈ b.divisors, ∑ c ∈ Finset.Ico 1 (M - b), ∑ e ∈ c.divisors, ∑ f ∈ (M - b - c).divisors, (d : K) * (e : K) * (f : K) * ((Gz u ((e : ℤ) + f + d) - Gz u ((e : ℤ) + f - d) + Gz u ((e : ℤ) - f + d) - Gz u ((e : ℤ) - f - d) - 2 * Gz u ((e : ℤ) + d) + 2 * Gz u ((e : ℤ) - d) - 2 * Gz u ((f : ℤ) + d) + 2 * Gz u ((f : ℤ) - d) + 4 * Gz u (d : ℤ)) * Gz v (d : ℤ) - (Gz u ((e : ℤ) + d) - Gz u ((e : ℤ) - d) - 2 * Gz u (d : ℤ)) * (Gz v ((f : ℤ) + d) - Gz v ((f : ℤ) - d) - 2 * Gz v (d : ℤ)) - (Gz u ((f : ℤ) + d) - Gz u ((f : ℤ) - d) - 2 * Gz u (d : ℤ)) * (Gz v ((e : ℤ) + d) - Gz v ((e : ℤ) - d) - 2 * Gz v (d : ℤ)) + Gz u (d : ℤ) * (Gz v ((e : ℤ) + f + d) - Gz v ((e : ℤ) + f - d) + Gz v ((e : ℤ) - f + d) - Gz v ((e : ℤ) - f - d) - 2 * Gz v ((e : ℤ) + d) + 2 * Gz v ((e : ℤ) - d) - 2 * Gz v ((f : ℤ) + d) + 2 * Gz v ((f : ℤ) - d) + 4 * Gz v (d : ℤ)))) := by sorry
