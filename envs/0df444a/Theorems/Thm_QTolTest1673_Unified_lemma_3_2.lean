-- Prove2me | Theorems.Thm_QTolTest1673_Unified_lemma_3_2
-- name    : QTolTest1673.Unified.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:22:07.090352+00:00
-- url     : https://prove2.me/theorems/f8856c56-3416-4212-a5c0-464961aeb1bd
-- title:
--   Lemma 3.2 — the VC dimension of $\mathcal V_k^{\dim}$ and of $\mathcal V_k^{\mathrm{junta}}$ is $k$
-- statement:
--   Let $1\le k<n$. View the family $\mathcal V_k^{\dim}$ of all subspaces of $\mathbb F_2^n$ of dimension at most $k$, and the family $\mathcal V_k^{\mathrm{junta}}$ of coordinate subspaces $V_T=\{u:\operatorname{supp}(u)\subseteq T\}$ with $|T|\le k$, as families of subsets of $\Omega=\mathbb F_2^n$. A family shatters a finite $S\subseteq\Omega$ if every subset of $S$ is of the form $A\cap S$ with $A$ in the family; the VC dimension is the largest size of a shattered set. Then
--   $$\operatorname{VC}(\mathcal V_k^{\dim})=\operatorname{VC}(\mathcal V_k^{\mathrm{junta}})=k .$$
--
--   The bound is independent of $n$, so VC uniform convergence gives a number of Fourier samples independent of $n$, although the families have size growing with $n$.
--
--   Differences from the source:
--   - encoding: VC dimension of a family of subsets → `UnderstandingML.vcDim` (values in $\mathbb N\cup\{\infty\}$) of the family of indicator functions $u\mapsto\mathbf 1[u\in V]$; reason: Definition 3.1 with a set identified with its indicator; the value $k$ is finite
--   - encoding: coordinates $[n]=\{1,\dots,n\}$ → `Fin n` = $\{0,\dots,n-1\}$; reason: index base only; same instances
-- source:
--   Zekun Ye, Jialin Zhang, Quantum Tolerant Testing of Fourier Dimensionality and Juntas, STOC 2027 submission #1673 (October 2026), source.pdf SHA-256 5f8e9058de57e5bfe86cd485966905d576e77df38d613213662f8930b3e0e51e, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1673.pdf, Lemma 3.2 and Definition 3.1, p. 18

import Definitions.Def_QTolTest1673_Unified_Classes

namespace QTolTest1673.Unified

open FourierDimTesting102.Quantum

/-- Lemma 3.2, p. 18 (VC dimension of the two candidate families). For `1 ≤ k < n`, the family
`V_k^dim` of subspaces of `F₂ⁿ` of dimension at most `k`, and the family `V_k^junta` of
coordinate subspaces `V_T` with `|T| ≤ k`, viewed as families of subsets of `Ω = F₂ⁿ`, both
have VC dimension exactly `k`. -/
theorem lemma_3_2 (n k : ℕ) (hk : 1 ≤ k) (hkn : k < n) :
    UnderstandingML.vcDim (indicatorFamily (famDim n k)) = k ∧
      UnderstandingML.vcDim (indicatorFamily (famJunta n k)) = k := by sorry

end QTolTest1673.Unified
