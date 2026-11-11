-- Prove2me | Theorems.Thm_PPADSIS_SubexpSIS_corollary_7_9
-- name    : PPADSIS.SubexpSIS.corollary_7_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:50:11.148964+00:00
-- url     : https://prove2.me/theorems/9a040720-be4f-4457-88fd-f68abfd83296
-- title:
--   Corollary 7.9 (= Theorem 1.2) — subexponentially hard SIS implies a hard distribution of End-of-Metered-Line
-- statement:
--   Let $e,\nu$ be real constants with $0<e<5/9$ and $4e/5<\nu<1-e$. Assume Assumption 7.7 for $(e,\nu)$: for all parameter functions $n,m,q$ in the regime of Assumption 3.5 (with $n$ polynomially bounded and $n\ge\lambda^{\Omega(1)}$, $\beta:=2^{n^e}$, $m$ polynomially bounded, $q$ a power of two with $n\sqrt m\cdot\beta\le q\le2^{\mathrm{poly}(n)}$) that also satisfy $q\le2^{2\lceil n^e\rceil}$, $\mathrm{SIS}_{n,m,q,\beta}$ (max-entry norm) is $2^{n^\nu}$-hard. Then there is a hard distribution of EOML:
--   $$\text{Assumption 7.7}(e,\nu)\ \Longrightarrow\ \exists D:\ D\text{ is a hard distribution of End-of-Metered-Line}.$$
--   That is, one probabilistic polynomial-time sampler $D(1^\lambda)$ such that, for all sufficiently large $\lambda$, every instance $(S,P,M,v_0)$ it outputs satisfies $P(v_0)=v_0\ne S(v_0)$ and $M(v_0)=1$, and every non-uniform family of probabilistic polynomial-size circuits, given the instance's description, outputs a solution (of any of the three types of Definition 3.2) with negligible probability.
--
--   This is the paper's title result, formally Theorem 1.2: SIS alone, at subexponential hardness, makes $\mathsf{PPAD}$ (indeed its subclass $\mathsf{CLS}$) hard on average. For instance $e=\nu=1/3$ is allowed.
--
--   Differences from the source:
--   - reading: the parameter conditions of Assumptions 3.5 and 7.7 ($q$ a power of two, $n\sqrt m\,\beta\le q$, $q\le2^{\mathrm{poly}(n)}$, $q\le2^{2\lceil n^e\rceil}$) → required at every $\lambda$; $n\ge\lambda^{\Omega(1)}$ → $n(\lambda)\ge\lambda^c$ for some real $c>0$ and all large $\lambda$; $\mathrm{poly}(n)$ → $(n+2)^k$; reason: requiring them only eventually would quantify over more parameter functions and strengthen the hypothesis.
--   - encoding: instances, matrices and vectors are handed over as fixed injective binary descriptions (`EOMLInstance.enc`, `encMat`, `encIntVec`); an adversary output that is not the code of a vector or not a vertex of length $m$ fails; reason: the paper fixes no encoding.
--   - encoding: the meter $M:\{0,1\}^m\to[0,2^m]$ → a circuit with $m+1$ outputs read big-endian and capped at $2^m$; reason: every meter of the paper is represented, and every circuit is a valid meter.
--   - encoding: Boolean circuits over $\{0,1,\neg,\wedge,\vee\}$ with distinct output wires and size = input wires + gates; adversaries with one circuit per $(\lambda,\text{input length})$; reason: the paper's circuit model; the adversary classes give the same hardness notions (see `Adversary`).
--   - encoding: "sampled in polynomial time" → one `PolyTimeComputable` machine reading $1^\lambda$ and $p(\lambda)$ coins for a polynomial $p\in\mathbb N[X]$, probabilities as exact averages over coins; reason: the paper's uniform probabilistic polynomial-time sampler.
-- source:
--   Choudhuri, PPAD Hardness from SIS, STOC 2027 submission (manuscript sha256 17abad73…), p. 59, Corollary 7.9 (informal Theorem 1.2, p. 2)

import Mathlib
import Definitions.Def_PPADSIS_SubexpSIS_EOML
import Definitions.Def_PPADSIS_SubexpSIS_Assumption

namespace PPADSIS.SubexpSIS

theorem corollary_7_9 (e ν : ℝ) (he₀ : 0 < e) (he₁ : e < 5 / 9) (hν₀ : 4 * e / 5 < ν)
    (hν₁ : ν < 1 - e) (h77 : Assumption77 e ν) :
    ∃ D : CoinAlg unary, IsHardEOML D := by sorry

end PPADSIS.SubexpSIS
