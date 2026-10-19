-- Prove2me | Theorems.Thm_QAlgorithms_Papers_RoadmapD08_sunWootters_sampling_and_optimization
-- name    : QAlgorithms.Papers.RoadmapD08.sunWootters_sampling_and_optimization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:44:43.108987+00:00
-- url     : https://prove2.me/theorems/8cc72bf1-b39e-4608-93f4-92ea3a7e904d
-- title:
--   Sun–Wootters sampling: exact ideal branch, efficient approximate sampler, and both balanced optimization consequences
-- statement:
--   Let $p$ be prime, $1\le n<m\le p$, and let $\alpha_1,\ldots,\alpha_m\in\mathbb F_p$ be distinct public evaluation points. Every hidden set $S_i\subset\mathbb F_p$ has the same known cardinality $c$, with $0<c<p$. Put $\rho=c/p$, $B_{ij}=\alpha_i^j$ for $j=0,\ldots,n-1$, and $H=B^{\mathsf T}$. A coefficient vector $x\in\mathbb F_p^n$ represents the polynomial $Q_x(T)=\sum_{j=0}^{n-1}x_jT^j$; its satisfaction ratio is $s(x)=m^{-1}|\{i:Q_x(\alpha_i)\in S_i\}|$. Access is through the indexed XOR oracle $O_S|i,a,b\rangle=|i,a,b\oplus\mathbf1_{a\in S_i}\rangle$, with arbitrary full unitary behavior on invalid encodings.
--
--   For an integer cutoff $3\le\ell\le m$, set $\sigma=\lfloor\log\log\ell\rfloor$, $K=\{k\in\{0,\ldots,m\}:\ell-\sigma\le k\le\ell\}$, and $u_k=\binom mk^{-1/2}\mathbf1_{k\in K}$. Define $g_i(a)=(\mathbf1_{a\in S_i}-\rho)/\sqrt{\rho(1-\rho)}$, $\widehat g_i(z)=p^{-1}\sum_a g_i(a)e^{-2\pi iaz/p}$, $q_k(x)=\sum_{|T|=k}\prod_{i\in T}g_i((Bx)_i)$ and $F(x)=\sum_{k\in K}u_kq_k(x)$. On its positive-denominator domain the Sun–Wootters law is
--
--   $$P_u(x)=\frac{|F(x)|^2}{\sum_z|F(z)|^2}.$$
--
--   Write $a_y=u_{\mathrm{wt}(y)}\prod_{i:y_i\ne0}\widehat g_i(y_i)$, $A_s=\sum_{Hy=s,\,\mathrm{wt}(y)\in K}a_y$, $Z_0=\sum_y|a_y|^2$, and $Z_I=\sum_s|A_s|^2$. Suppose $Z_0>0$ and the target denominator is positive. For every complete duplicate-free canonical shell list, padded to the same $L=2^q$ slots for every syndrome, the ideal attempt prepares $Z_0^{-1/2}\sum_y a_y|y,Hy\rangle$, reversibly indexes and erases the error, applies $H^{\otimes q}$ to the index, and postselects $(J,Q)=(0^q,1)$ using a match flag. It then applies the positive-character Fourier transform on the syndrome. Its success and conditional law satisfy
--
--   $$p_{\rm ideal}=\frac{Z_I}{LZ_0},\qquad \mathcal L(x\mid\text{success})=P_u,\qquad Z_I=p^{-n}\sum_x|F(x)|^2.$$
--
--   This finite identity preserves cancellation within fibers and asserts no running-time bound for an arbitrary unpriced list. For normalized ideal and implemented full-register states, ideal success at least $1/(2L)$, vector error at most $\min\{1/(8L),\eta/(4\sqrt{2L})\}$, and final Fourier operator error at most $\eta/2$, implemented success is at least $1/(4L)$ and conditional total variation error is at most $\eta$.
--
--   Now consider public parameter families with $m\to\infty$, $n/m\to r=2\mu\in(0,1]$, and $c/p\to1/2$. Constants, programs and preprocessing are uniform over all sets of the promised cardinality and every supplied membership oracle. Let $h(t)=-t\log t-(1-t)\log(1-t)$, using natural logarithms and $0\log0=0$, and define
--
--   $$E(\mu,\delta)=(\mu+\delta)h\!\left(\frac\mu{\mu+\delta}\right)+(1-\mu-\delta)h\!\left(\frac\mu{1-\mu-\delta}\right)-h(2\mu),$$
--   $$G(\mu,\lambda)=(1-2\mu)\log2+h(2\mu)-(4\mu-1)h\!\left(\frac\lambda{4\mu-1}\right)-(2-4\mu)h\!\left(\frac{2\mu-\lambda}{2-4\mu}\right)+\lambda\log(2/\pi).$$
--
--   All denominators in these ratios must be nonzero and all entropy arguments must belong to $[0,1]$. Fix $0<\mu<1/2$, a positive rational $\delta\le1/2-\mu$, and $\lambda$ in that domain with $E+G<0$ and $\mu+\delta<1-\sqrt{1-2\mu}$. Put $\ell_m=\min\{\lfloor n/2+\delta m\rfloor,\lfloor m/2\rfloor\}$. Eventually the target is well defined, complete canonical lists admit one polynomial common padding length, and ideal success is at least $1/(2L)$. For every $\eta,\beta\in(0,1/2)$, a uniform quantum algorithm with time polynomial in $m,\log p,\log(1/\eta),\log(1/\beta)$ satisfies
--
--   $$\Pr[x=\bot]\le\beta,\qquad \operatorname{TV}(\mathcal L(x\mid x\ne\bot),P_{u,m})\le\eta.$$
--
--   For every fixed default vector, the defaulted law has total variation distance at most $\eta+\beta$ from $P_{u,m}$ and expected score at least $\mathrm{SCL}_{1/2}(\mu+\delta)-a_m-\eta-\beta$, for some nonnegative $a_m\to0$ independent of the hidden sets; here $\mathrm{SCL}_{1/2}(t)=1/2+\sqrt{t(1-t)}$ on $[0,1/2]$. Preprocessing, synthesized gates, queries, measurements, reversible/classical work, and capped restarts are counted.
--
--   The two balanced consequences are retained:
--
--   1. For each fixed $r\in[249/400,1)$, a gap $\gamma_r>0$ and a uniform algorithm are chosen before the sets or parameter family. Eventually $\mathbb E[s(x)]\ge\mathrm{SCL}_{1/2}(r/2)+\gamma_r$. For every fixed $\varepsilon>0$ and $\beta\in(0,1)$, polynomially many samples give $s(x)\ge\mathrm{SCL}_{1/2}(r/2)+\gamma_r-\varepsilon$ with probability at least $1-\beta$.
--   2. For every limiting $r\in[3/4,1]$, a uniform polynomial-time algorithm has nonnegative $e_m,b_m\to0$ with $\Pr[s(x)\ge1-e_m]\ge1-b_m$. Its construction uses $n'_m=\min\{n,\lfloor3m/4\rfloor\}$, $\ell_J=\min\{\lfloor m/2\rfloor,\lceil m-\sqrt{(m-n'_m-1)m}\rceil-1\}$, error and failure targets $m^{-2}$, and appends zero coefficients. It approaches the endpoint parameters $(\mu,\delta,\lambda)=(3/8,1/8,99/250)$ from the strict finite Johnson range, without asserting finite-length perfect satisfaction.
--
--   These conclusions turn the Sun–Wootters distributional improvement into efficient worst-case quantum optimization.
--
--   **Formalization Note** Theorem 7.1's printed “For each family member” is clarified to an eventual guarantee, matching its proof's positivity and decoder-feasibility bounds. This is an explicit proof-based scope clarification awaiting independent moderation. The finite exact identity is separate from the approximate universal-gate implementation. The paper's operator called inverse QFT has positive character and equals the frozen positive-sign QFT convention.
--
--   **Correction to the printed source.**
--
--   Printed: For each family member put ... and define Pu,m by equations (11) to (13) with largest active weight ell_m. Then ... there is a uniform bounded-error quantum algorithm.
--
--   Corrected: The finite target is defined on its positive-denominator and cutoff-at-least-three domain, and the sampling guarantees hold for every sufficiently large public parameter-family member.
--
--   Reason: Theorem 7.1 itself invokes the finite Johnson inequality and postselection estimate only for all sufficiently large m. Lemmas 3.2 and 6.4 are eventual, while equation (11) uses log log ell; early undefined targets cannot be normalized by total division.
-- source:
--   Efficient Exact Quantum Sampling from the Sun-Wootters Distribution for Optimal Polynomial Intersection, arXiv:2607.16541v2, Theorem 1.1 (continues on PDF p.4); formal Theorem 7.1 and Corollaries 8.6, 8.8, PDF p. 3. https://arxiv.org/abs/2607.16541v2 . PDF SHA-256: bf815612f36916d97f6a342f88ef7a81a11ce7b291250428ed038139ff368293.

import Definitions.Def_QAlgorithms_Defs_SunWoottersAsymptotics
import Definitions.Def_QAlgorithms_Papers_RoadmapD08_Model
set_option autoImplicit false

noncomputable section

attribute [local instance] Classical.propDecidable

open Filter
open scoped Matrix ENNReal

namespace QAlgorithms.Papers.RoadmapD08

open QAlgorithms.SunWootters

/-- Jo, arXiv:2607.16541v2, Theorem 1.1, PDF pp.3--4 (printed pp.1--2), through
Theorem 5.2, Corollary 6.6, Theorem 7.1, Corollaries 8.6 and 8.8 (PDF pp.13,16--17,21--23).
All headline clauses are retained: finite exact ideal sampling, finite-precision uniform
sampling, constant semicircle improvement, and high-probability asymptotic perfection.

Explicit proof-based clarification awaiting independent moderation: Theorem 7.1's printed
"For each family member" is made eventual because its proof only establishes finite decoder
feasibility, positivity and nonzero log-log shells eventually. Fourier translation: the
paper's final inverse QFT has positive character and is frozen `qftMatrix`; local Fourier
coefficients have negative phase. Exactness refers to the ideal successful branch.
The endpoint construction uses (mu,delta,lambda)=(3/8,1/8,99/250) in its analytic estimate,
and the strict finite cutoff (69), not a constant Johnson slack at r=3/4. -/
theorem sunWootters_sampling_and_optimization :
    d08FiniteExactClause ∧ d08PrecisionClause ∧ d08FixedSlackClause ∧
      d08StrictImprovementClause ∧ d08EndpointClause := by sorry

end QAlgorithms.Papers.RoadmapD08
